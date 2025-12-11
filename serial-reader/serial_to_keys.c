#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <glob.h>
#include <fcntl.h>
#include <termios.h>
#include <unistd.h>
#include <ApplicationServices/ApplicationServices.h>

static void list_ports(const glob_t *g_tty, const glob_t *g_cu) {
    printf("Available serial ports:\n");
    size_t idx = 0;

    for (size_t i = 0; i < g_tty->gl_pathc; i++)
        printf("%zu: %s\n", idx++, g_tty->gl_pathv[i]);

    for (size_t i = 0; i < g_cu->gl_pathc; i++)
        printf("%zu: %s\n", idx++, g_cu->gl_pathv[i]);
}

static char* choose_port(const glob_t *g_tty, const glob_t *g_cu) {
    size_t total = g_tty->gl_pathc + g_cu->gl_pathc;

    if (total == 0) {
        printf("No serial ports found.\n");
        exit(1);
    }

    printf("Select a port number: ");
    int choice;
    if (scanf("%d", &choice) != 1 || choice < 0 || (size_t)choice >= total) {
        printf("Invalid selection.\n");
        exit(1);
    }

    if ((size_t)choice < g_tty->gl_pathc)
        return g_tty->gl_pathv[choice];
    else
        return g_cu->gl_pathv[choice - g_tty->gl_pathc];
}

static void send_keystroke(char c) {
    // Create a keyboard event for the character
    UniChar uni = (UniChar)c;
    CGEventRef keyDown = CGEventCreateKeyboardEvent(NULL, 0, true);
    CGEventRef keyUp   = CGEventCreateKeyboardEvent(NULL, 0, false);

    if (!keyDown || !keyUp)
        return;

    CGEventKeyboardSetUnicodeString(keyDown, 1, &uni);
    CGEventKeyboardSetUnicodeString(keyUp,   1, &uni);

    CGEventPost(kCGAnnotatedSessionEventTap, keyDown);
    CGEventPost(kCGAnnotatedSessionEventTap, keyUp);

    CFRelease(keyDown);
    CFRelease(keyUp);
}

int main() {
    glob_t g_tty = {0}, g_cu = {0};

    glob("/dev/tty.*", 0, NULL, &g_tty);
    glob("/dev/cu.*",  0, NULL, &g_cu);

    list_ports(&g_tty, &g_cu);
    char *port = choose_port(&g_tty, &g_cu);

    printf("Opening %s\n", port);
    int fd = open(port, O_RDWR | O_NOCTTY);
    if (fd == -1) {
        perror("open");
        return 1;
    }

    struct termios options;
    tcgetattr(fd, &options);

    cfsetispeed(&options, B115200);
    cfsetospeed(&options, B115200);

    options.c_cflag |= (CLOCAL | CREAD);
    options.c_cflag &= ~CSIZE;
    options.c_cflag |= CS8;
    options.c_cflag &= ~PARENB;
    options.c_cflag &= ~CSTOPB;
    options.c_cflag &= ~CRTSCTS;

    options.c_lflag &= ~(ICANON | ECHO | ECHOE | ISIG);
    options.c_iflag &= ~(IXON | IXOFF | IXANY);
    options.c_oflag &= ~OPOST;

    tcsetattr(fd, TCSANOW, &options);

    printf("Reading and sending keystrokes...\n");

    while (1) {
        char buf[256];
        int n = read(fd, buf, sizeof(buf));  // blocks
        if (n > 0) {
            for (int i = 0; i < n; i++)
                send_keystroke(buf[i]);
        } else if (n < 0) {
            perror("read");
            break;
        }
    }

    close(fd);
    globfree(&g_tty);
    globfree(&g_cu);
    return 0;
}

