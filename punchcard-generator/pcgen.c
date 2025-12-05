#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>

#define CARD_WIDTH 7.375
#define CARD_HEIGHT 3.25

#define CORNER_RADIUS 0.25
#define CUT_HEIGHT 0.4375
#define CUT_WIDTH 0.25

#define HOLE_WIDTH 0.055
#define HOLE_HEIGHT 0.125

#define COL_SPACING 0.087
#define ROW_SPACING 0.25

#define CARD_MARGIN 0.25
#define IMG_MARGIN 0.25

double scale_factor = 2000.0;

const int hollerith[256][7] = {
    { 0, 2, 11, 10, 3, -1 },
    { 0, 11, 3, -1 },
    { 0, 11, 4, -1 },
    { 0, 11, 5, -1 },
    { 11, 9, -1 },
    { 2, 11, 10, 7, -1 },
    { 2, 11, 10, 8, -1 },
    { 2, 11, 10, 9, -1 },
    { 1, 11, 8, -1 },
    { 0, 11, 7, -1 },
    { 2, 11, 7, -1 },
    { 0, 11, 10, 5, -1 },
    { 0, 11, 10, 6, -1 },
    { 0, 11, 10, 7, -1 },
    { 0, 11, 10, 8, -1 },
    { 0, 11, 10, 9, -1 },
    { 0, 1, 11, 10, 3, -1 },
    { 1, 11, 3, -1 },
    { 1, 11, 4, -1 },
    { 1, 11, 5, -1 },
    { 11, 10, 6, -1 },
    { 11, 10, 7, -1 },
    { 11, 4, -1 },
    { 2, 11, 8, -1 },
    { 1, 11, 10, -1 },
    { 1, 11, 10, 3, -1 },
    { 11, 10, 9, -1 },
    { 2, 11, 9, -1 },
    { 1, 11, 10, 6, -1 },
    { 1, 11, 10, 7, -1 },
    { 1, 11, 10, 8, -1 },
    { 1, 11, 10, 9, -1 },
    { -1 },
    { 0, 10, 9, -1 },
    { 10, 9, -1 },
    { 10, 5, -1 },
    { 1, 10, 5, -1 },
    { 2, 10, 6, -1 },
    { 0, -1 },
    { 10, 7, -1 },
    { 0, 10, 7, -1 },
    { 1, 10, 7, -1 },
    { 1, 10, 6, -1 },
    { 0, 10, 8, -1 },
    { 2, 10, 5, -1 },
    { 1, -1 },
    { 0, 10, 5, -1 },
    { 2, 3, -1 },
    { 2, -1 },
    { 3, -1 },
    { 4, -1 },
    { 5, -1 },
    { 6, -1 },
    { 7, -1 },
    { 8, -1 },
    { 9, -1 },
    { 10, -1 },
    { 11, -1 },
    { 10, 4, -1 },
    { 1, 10, 8, -1 },
    { 0, 10, 6, -1 },
    { 10, 8, -1 },
    { 2, 10, 8, -1 },
    { 2, 10, 9, -1 },
    { 10, 6, -1 },
    { 0, 3, -1 },
    { 0, 4, -1 },
    { 0, 5, -1 },
    { 0, 6, -1 },
    { 0, 7, -1 },
    { 0, 8, -1 },
    { 0, 9, -1 },
    { 0, 10, -1 },
    { 0, 11, -1 },
    { 1, 3, -1 },
    { 1, 4, -1 },
    { 1, 5, -1 },
    { 1, 6, -1 },
    { 1, 7, -1 },
    { 1, 8, -1 },
    { 1, 9, -1 },
    { 1, 10, -1 },
    { 1, 11, -1 },
    { 2, 4, -1 },
    { 2, 5, -1 },
    { 2, 6, -1 },
    { 2, 7, -1 },
    { 2, 8, -1 },
    { 2, 9, -1 },
    { 2, 10, -1 },
    { 2, 11, -1 },
    { 0, 10, 4, -1 },
    { 2, 10, 4, -1 },
    { 1, 10, 4, -1 },
    { 1, 10, 9, -1 },
    { 2, 10, 7, -1 },
    { 10, 3, -1 },
    { 0, 2, 3, -1 },
    { 0, 2, 4, -1 },
    { 0, 2, 5, -1 },
    { 0, 2, 6, -1 },
    { 0, 2, 7, -1 },
    { 0, 2, 8, -1 },
    { 0, 2, 9, -1 },
    { 0, 2, 10, -1 },
    { 0, 2, 11, -1 },
    { 0, 1, 3, -1 },
    { 0, 1, 4, -1 },
    { 0, 1, 5, -1 },
    { 0, 1, 6, -1 },
    { 0, 1, 7, -1 },
    { 0, 1, 8, -1 },
    { 0, 1, 9, -1 },
    { 0, 1, 10, -1 },
    { 0, 1, 11, -1 },
    { 1, 2, 4, -1 },
    { 1, 2, 5, -1 },
    { 1, 2, 6, -1 },
    { 1, 2, 7, -1 },
    { 1, 2, 8, -1 },
    { 1, 2, 9, -1 },
    { 1, 2, 10, -1 },
    { 1, 2, 11, -1 },
    { 0, 2, -1 },
    { 0, 1, -1 },
    { 1, 2, -1 },
    { 1, 2, 3, -1 },
    { 0, 11, 9, -1 },
    { 1, 2, 11, 10, 3, -1 },
    { 2, 11, 3, -1 },
    { 2, 11, 4, -1 },
    { 2, 11, 5, -1 },
    { 2, 11, 6, -1 },
    { 1, 11, 7, -1 },
    { 0, 11, 8, -1 },
    { 1, 11, 9, -1 },
    { 2, 11, 10, -1 },
    { 2, 11, 10, 3, -1 },
    { 2, 11, 10, 4, -1 },
    { 2, 11, 10, 5, -1 },
    { 2, 11, 10, 6, -1 },
    { 0, 11, 10, 3, -1 },
    { 0, 11, 10, 4, -1 },
    { 1, 11, 10, 5, -1 },
    { 0, 1, 2, 11, 10, 3, -1 },
    { 11, 3, -1 },
    { 1, 11, 10, 4, -1 },
    { 11, 5, -1 },
    { 11, 6, -1 },
    { 11, 7, -1 },
    { 11, 8, -1 },
    { 0, 11, 10, -1 },
    { 11, 10, -1 },
    { 11, 10, 3, -1 },
    { 11, 10, 4, -1 },
    { 11, 10, 5, -1 },
    { 0, 11, 6, -1 },
    { 1, 11, 6, -1 },
    { 11, 10, 8, -1 },
    { 1, 2, 11, 3, -1 },
    { 0, 2, 11, 3, -1 },
    { 0, 2, 11, 4, -1 },
    { 0, 2, 11, 5, -1 },
    { 0, 2, 11, 6, -1 },
    { 0, 2, 11, 7, -1 },
    { 0, 2, 11, 8, -1 },
    { 0, 2, 11, 9, -1 },
    { 0, 2, 11, 10, -1 },
    { 0, 10, 3, -1 },
    { 0, 1, 11, 3, -1 },
    { 0, 1, 11, 4, -1 },
    { 0, 1, 11, 5, -1 },
    { 0, 1, 11, 6, -1 },
    { 0, 1, 11, 7, -1 },
    { 0, 1, 11, 8, -1 },
    { 0, 1, 11, 9, -1 },
    { 0, 1, 11, 10, -1 },
    { 1, 10, 3, -1 },
    { 1, 2, 11, 4, -1 },
    { 1, 2, 11, 5, -1 },
    { 1, 2, 11, 6, -1 },
    { 1, 2, 11, 7, -1 },
    { 1, 2, 11, 8, -1 },
    { 1, 2, 11, 9, -1 },
    { 1, 2, 11, 10, -1 },
    { 2, 10, 3, -1 },
    { 0, 1, 2, -1 },
    { 0, 1, 2, 11, 3, -1 },
    { 0, 1, 2, 11, 4, -1 },
    { 0, 1, 2, 11, 5, -1 },
    { 0, 1, 2, 11, 6, -1 },
    { 0, 1, 2, 11, 7, -1 },
    { 0, 1, 2, 11, 8, -1 },
    { 0, 1, 2, 11, 9, -1 },
    { 0, 1, 2, 11, 10, -1 },
    { 0, 2, 10, 3, -1 },
    { 0, 2, 10, 4, -1 },
    { 0, 2, 10, 5, -1 },
    { 0, 2, 10, 6, -1 },
    { 0, 2, 10, 7, -1 },
    { 0, 2, 10, 8, -1 },
    { 0, 2, 10, 9, -1 },
    { 0, 1, 10, 3, -1 },
    { 0, 1, 10, 4, -1 },
    { 0, 1, 10, 5, -1 },
    { 0, 1, 10, 6, -1 },
    { 0, 1, 10, 7, -1 },
    { 0, 1, 10, 8, -1 },
    { 0, 1, 10, 9, -1 },
    { 1, 2, 10, 3, -1 },
    { 1, 2, 10, 4, -1 },
    { 1, 2, 10, 5, -1 },
    { 1, 2, 10, 6, -1 },
    { 1, 2, 10, 7, -1 },
    { 1, 2, 10, 8, -1 },
    { 1, 2, 10, 9, -1 },
    { 0, 1, 2, 10, 3, -1 },
    { 0, 1, 2, 3, -1 },
    { 0, 1, 2, 4, -1 },
    { 0, 1, 2, 5, -1 },
    { 0, 1, 2, 6, -1 },
    { 0, 1, 2, 7, -1 },
    { 0, 1, 2, 8, -1 },
    { 0, 1, 2, 9, -1 },
    { 0, 1, 2, 10, -1 },
    { 0, 1, 2, 11, -1 },
    { 0, 1, 2, 10, 4, -1 },
    { 0, 1, 2, 10, 5, -1 },
    { 0, 1, 2, 10, 6, -1 },
    { 0, 1, 2, 10, 7, -1 },
    { 0, 1, 2, 10, 8, -1 },
    { 0, 1, 2, 10, 9, -1 },
    { 0, 2, 11, 10, 4, -1 },
    { 0, 2, 11, 10, 5, -1 },
    { 0, 2, 11, 10, 6, -1 },
    { 0, 2, 11, 10, 7, -1 },
    { 0, 2, 11, 10, 8, -1 },
    { 0, 2, 11, 10, 9, -1 },
    { 0, 1, 11, 10, 4, -1 },
    { 0, 1, 11, 10, 5, -1 },
    { 0, 1, 11, 10, 6, -1 },
    { 0, 1, 11, 10, 7, -1 },
    { 0, 1, 11, 10, 8, -1 },
    { 0, 1, 11, 10, 9, -1 },
    { 1, 2, 11, 10, 4, -1 },
    { 1, 2, 11, 10, 5, -1 },
    { 1, 2, 11, 10, 6, -1 },
    { 1, 2, 11, 10, 7, -1 },
    { 1, 2, 11, 10, 8, -1 },
    { 1, 2, 11, 10, 9, -1 },
    { 0, 1, 2, 11, 10, 4, -1 },
    { 0, 1, 2, 11, 10, 5, -1 },
    { 0, 1, 2, 11, 10, 6, -1 },
    { 0, 1, 2, 11, 10, 7, -1 },
    { 0, 1, 2, 11, 10, 8, -1 },
    { 0, 1, 2, 11, 10, 9, -1 }
};

int scale(double original) {
    return round(original * scale_factor);
}

int inch_to_image(double original) {
    return round((original + IMG_MARGIN) * scale_factor);
}

void print_prologue(void) {
    int card_begin_x = inch_to_image(0.0);
    int card_begin_y = inch_to_image(0.0);
    int card_end_x = inch_to_image(CARD_WIDTH);
    int card_end_y = inch_to_image(CARD_HEIGHT);
    int cut_x = inch_to_image(CUT_WIDTH);
    int cut_y = inch_to_image(CUT_HEIGHT);
    int corner_radius = scale(CORNER_RADIUS);
    int left_corner_x = card_begin_x + corner_radius;
    int right_corner_x = card_end_x - corner_radius;
    int top_corner_y = card_begin_y + corner_radius;
    int bottom_corner_y = card_end_y - corner_radius;


    printf(
        "<svg version=\"1.1\"\n"
        "     width=\"%d\" height=\"%d\"\n"
        "     xmlns=\"http://www.w3.org/2000/svg\">\n\n"
        "    <path\n"
        "        d=\"M %d %d\n"
        "           L %d %d\n"
        "           H %d\n"
        "           A %d %d 0 0 1 %d %d\n"
        "           V %d\n"
        "           A %d %d 0 0 1 %d %d\n"
        "           H %d\n"
        "           A %d %d 0 0 1 %d %d\n"
        "           Z\"\n"
        "        fill=\"transparent\"\n"
        "        stroke=\"black\" />\n\n",
        scale(CARD_WIDTH + IMG_MARGIN * 2), scale(CARD_HEIGHT + IMG_MARGIN * 2),
        card_begin_x, cut_y,
        cut_x, card_begin_y,
        right_corner_x,
        corner_radius, corner_radius, card_end_x, top_corner_y,
        bottom_corner_y,
        corner_radius, corner_radius, right_corner_x, card_end_y,
        left_corner_x,
        corner_radius, corner_radius, card_begin_x, bottom_corner_y
    );
}

void punch_hole(int column, int row) {
    double hole_center_x = column * COL_SPACING + CARD_MARGIN;
    double hole_center_y = row * ROW_SPACING + CARD_MARGIN;
    int hole_x_start = inch_to_image(hole_center_x - HOLE_WIDTH / 2);
    int hole_y_start = inch_to_image(hole_center_y - HOLE_HEIGHT / 2);
    int hole_width = scale(HOLE_WIDTH);
    int hole_height = scale(HOLE_HEIGHT);
    printf("    <rect x=\"%d\" y=\"%d\" width=\"%d\" height=\"%d\" fill=\"transparent\" stroke=\"black\" />\n",
        hole_x_start, hole_y_start, hole_width, hole_height);
}

void punch_char(int column, char c) {
    for (const int* hole_to_punch = hollerith[(unsigned char)c]; *hole_to_punch >= 0; hole_to_punch++) {
        punch_hole(column, *hole_to_punch);
    }
}

void punch_str(char* str) {
    for (size_t i = 0; str[i] != '\0'; i++) {
        punch_char(i, str[i]);
    }
}

void print_epilogue(void) {
    printf("\n</svg>\n");
}

int main(int argc, char** argv) {
    int c;

    while ((c = getopt(argc, argv, "s:")) != -1) {
        switch (c) {
            case 's':
                scale_factor = atof(optarg);
                if (!isnormal(scale_factor) || scale_factor <= 0) {
                    fprintf(stderr, "Invalid scale factor: %f\n", scale_factor);
                    exit(1);
                }
                break;
            default:
                printf("?? getopt returned character code 0%o ??\n", c);
        }
    }

    char* str_to_print;
    if (optind < argc) {
        str_to_print = argv[optind];
    } else {
        str_to_print = "Hello world! 0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz#<_>+";
    }

    size_t data_len = strlen(str_to_print);
    if (data_len > 80) {
        fprintf(stderr, "Data too long (max 80 columns, data is %zu bytes)\n", data_len);
    }

    print_prologue();
    punch_str(str_to_print);
    print_epilogue();
}
