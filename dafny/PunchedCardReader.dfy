include "Utilities.dfy"
include "PhotodiodeDriver.dfy"
include "CardProcessor.dfy"
include "StreamProcessor.dfy"

module PunchedCardReaderModule {
  import Utils = UtilitiesModule
  import PD = PhotodiodeDriverModule
  import CP = CardProcessorModule
  import SP = StreamProcessorModule

  datatype RunTickResult = RunTickResult(
    output_char: char,
    output_bytes: seq<bv8>,
    output_ready: bool
  )

  class PunchedCardReader {
    var photodiode_driver: PD.PhotodiodeDriver
    var card_processor: CP.CardProcessor
    var stream_processor: SP.StreamProcessor

    constructor ()
      ensures fresh(photodiode_driver)
      ensures fresh(card_processor)
      ensures fresh(stream_processor)
    {
      photodiode_driver := new PD.PhotodiodeDriver();
      card_processor := new CP.CardProcessor();
      stream_processor := new SP.StreamProcessor();
    }

    method RunTick(ADC_reading: Utils.arrayOfLength13<int>, mode_switch_is_binary: bool)
      returns (r : RunTickResult)
      modifies this,
               photodiode_driver, photodiode_driver.off_vals, photodiode_driver.punched,
               card_processor, card_processor.prev_punched,
               stream_processor
    {
      photodiode_driver.Tick(ADC_reading);

      var process_event_result := card_processor.ProcessEvent(photodiode_driver.punched);
      var column := process_event_result.column;
      var card_ended := process_event_result.card_ended;
      var output_ready := process_event_result.output_ready;

      if output_ready {
        var handle_input_result := stream_processor.HandleInput(mode_switch_is_binary, column, card_ended);
        var output_char := handle_input_result.output_char;
        var output_bytes := handle_input_result.output_bytes;
        var ready2 := handle_input_result.output_ready;
        r := RunTickResult(output_char, output_bytes, ready2);
      }
      else {
        r := RunTickResult('?', [], false);
      }
    }
  }

  class System {
    var reader: PunchedCardReader

    constructor ()
      ensures fresh(reader)
    {
      reader := new PunchedCardReader();
    }

    method {:main} Main()
      modifies this, reader,
               reader.photodiode_driver, reader.photodiode_driver.off_vals, reader.photodiode_driver.punched,
               reader.card_processor, reader.card_processor.prev_punched,
               reader.stream_processor
    {
      print "Punched Card Reader System Initialized.\n";

      var reading_inserted := new int[13](_ => 0);
      var run_tick_result := reader.RunTick(reading_inserted, false);
      var output_char := run_tick_result.output_char;
      var output_bytes := run_tick_result.output_bytes;
      var output_ready := run_tick_result.output_ready;

      if output_ready {
        print "Output Character: ", output_char, "\n";
      }
      else {
        print "No output on card insertion.\n";
      }
      print "System state transitioned to WAIT_FOR_COLUMN.\n";
    }
  }
}
