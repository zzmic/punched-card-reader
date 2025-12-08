include "Utilities.dfy"
include "PhotodiodeDriver.dfy"
include "CardProcessor.dfy"
include "StreamProcessor.dfy"

/**
  * Module for controlling the punched card reader.
  */
module PunchedCardReaderModule {
  import Utils = UtilitiesModule
  import PD = PhotodiodeDriverModule
  import CP = CardProcessorModule
  import SP = StreamProcessorModule

  /**
    * Result type for the `RunTick` method.
    */
  datatype RunTickResult = RunTickResult(
    output_char: char,
    output_bytes: seq<bv8>,
    output_ready: bool
  )

  /**
    * Class for controlling the punched card reader.
    */
  class PunchedCardReader {
    var photodiode_driver: PD.PhotodiodeDriver
    var card_processor: CP.CardProcessor
    var stream_processor: SP.StreamProcessor

    /**
      * Constructor that initializes the punched card reader.
      */
    constructor ()
      ensures fresh(photodiode_driver)
      ensures fresh(card_processor)
      ensures fresh(stream_processor)
    {
      photodiode_driver := new PD.PhotodiodeDriver();
      card_processor := new CP.CardProcessor();
      stream_processor := new SP.StreamProcessor();
    }

    /**
      * Run a tick of the punched card reader with the given ADC reading and stream mode.
      *
      * @param ADC_reading An array of length 13 representing the current ADC readings from the photodiodes.
      * @param mode The current stream mode (`TEXT` or `BINARY`).
      * @returns A `RunTickResult` containing the output character, output bytes, and output ready flag.
      */
    method RunTick(ADC_reading: Utils.arrayOfLength13<int>, mode: SP.StreamMode) returns (res : RunTickResult)
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
        var handle_input_result := stream_processor.HandleInput(mode, column, card_ended);
        var output_char := handle_input_result.output_char;
        var output_bytes := handle_input_result.output_bytes;
        var output_ready2 := handle_input_result.output_ready;
        res := RunTickResult(output_char, output_bytes, output_ready2);
      }
      else {
        res := RunTickResult('?', [], false);
      }
    }
  }
}
