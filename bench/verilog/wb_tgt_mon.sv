//###############################################################################
//# WbXbc - Wishbone Target Monitor Assertions (Pipelined)                      #
//###############################################################################
//#    Copyright 2018 Dirk Heisswolf                                            #
//#    This file is part of the WbXbc project.                                  #
//#                                                                             #
//#    WbXbc is free software: you can redistribute it and/or modify            #
//#    it under the terms of the GNU General Public License as published by     #
//#    the Free Software Foundation, either version 3 of the License, or        #
//#    (at your option) any later version.                                      #
//#                                                                             #
//#    WbXbc is distributed in the hope that it will be useful,                 #
//#    but WITHOUT ANY WARRANTY; without even the implied warranty of           #
//#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            #
//#    GNU General Public License for more details.                             #
//#                                                                             #
//#    You should have received a copy of the GNU General Public License        #
//#    along with WbXbc.  If not, see <http://www.gnu.org/licenses/>.           #
//###############################################################################
//# Description:                                                                #
//#    This module contains contraints and assertions to monitor a pipelined    #
//#    Wishbone target for protocol violations.                                 #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   October 12, 2018                                                          #
//#      - Initial release                                                      #
//#   November 9, 2018                                                          #
//#      - Disableing assertions and constraints in reset                       #
//#      - Added status signals to constraint FSM states                        #
//###############################################################################
`default_nettype none

module wb_tgt_mon
  #(parameter ADR_WIDTH   = 16,                              //width of the address bus
    parameter DAT_WIDTH   = 16,                              //width of each data bus
    parameter SEL_WIDTH   = 2,                               //number of data select lines
    parameter TGA_WIDTH   = 1,                               //number of address tags
    parameter TGC_WIDTH   = 1,                               //number of cycle tags
    parameter TGRD_WIDTH  = 1,                               //number of read data tags
    parameter TGWD_WIDTH  = 1)                               //number of write data tags

   (//Clock and reset
    //---------------
    input wire                             clk_i,            //module clock
    input wire                             async_rst_i,      //asynchronous reset
    input wire                             sync_rst_i,       //synchronous reset

   //Target interfaces
    //-----------------
    input  wire                            tgt_cyc_o,        //bus cycle indicator       +-
    input  wire                            tgt_stb_o,        //access request            |
    input  wire                            tgt_we_o,         //write enable              |
    input  wire                            tgt_lock_o,       //uninterruptable bus cycle | initiator
    input  wire [SEL_WIDTH-1:0]            tgt_sel_o,        //write data selects        | to
    input  wire [ADR_WIDTH-1:0]            tgt_adr_o,        //address bus               | target
    input  wire [DAT_WIDTH-1:0]            tgt_dat_o,        //write data bus            |
    input  wire [TGA_WIDTH-1:0]            tgt_tga_o,        //propagated address tags   |
    input  wire [TGC_WIDTH-1:0]            tgt_tgc_o,        //bus cycle tags            |
    input  wire [TGWD_WIDTH-1:0]           tgt_tgd_o,        //write data tags           +-
    input  wire                            tgt_ack_i,        //bus cycle acknowledge     +-
    input  wire                            tgt_err_i,        //error indicator           | target
    input  wire                            tgt_rty_i,        //retry request             | to
    input  wire                            tgt_stall_i,      //access delay              | initiator
    input  wire [DAT_WIDTH-1:0]            tgt_dat_i,        //read data bus             |
    input  wire [TGRD_WIDTH-1:0]           tgt_tgd_i,        //read data tags            +-

    //Testbench status signals
    //------------------------
    output wire                            tb_fsm_reset,     //FSM in RESET state
    output wire                            tb_fsm_idle,      //FSM in IDLE state
    output wire                            tb_fsm_busy);     //FSM in BUSY state

   //Abbreviations
   wire                                    rst = |{async_rst_i, sync_rst_i};            //reset
   wire                                    req = &{~tgt_stall_i, tgt_cyc_o, tgt_stb_o}; //request
   wire                                    ack = |{tgt_ack_i, tgt_err_i, tgt_rty_i};    //acknowledge

   //Simplify counter examples (only toggle at clock events)
   //=======================================================
   always @($global_clock)
     if (!$rose(clk_i))
       begin
          assume ($stable(tgt_ack_i));        //bus cycle acknowledge
          assume ($stable(tgt_err_i));        //error indicator
          assume ($stable(tgt_rty_i));        //retry request
          assume ($stable(tgt_stall_i));      //access delay
          assume ($stable(tgt_dat_i));        //read data bus
          assume ($stable(tgt_tgd_i));        //read data tags
       end // if (!$rose(clk_i))

   //State Machine
   //=============
   //        _______     ______      req       ______
   // rst   /       \   /      \------------->/      \
   //  O--->| RESET |-->| IDLE |              | BUSY |
   //       \_______/   \______/<-------------\______/
   //                              ~req & ack
   //State encoding
   parameter STATE_RESET = 2'b00;
   parameter STATE_IDLE  = 2'b01;
   parameter STATE_BUSY  = 2'b10;
   //State variable
   reg          [1:0]                           state_reg;
   reg          [1:0]                           state_next;
   always @(posedge async_rst_i or posedge clk_i)
     if (async_rst_i)                                        //asynchronous reset
       state_reg <= STATE_RESET;
     else if (sync_rst_i)                                    //synchronous reset
       state_reg <= STATE_RESET;
     else
       state_reg <= state_next;                              //state transition
   //State transitions
   always @*
     begin
        //Default transition
        state_next = state_reg; //remain in current state
        case (state_reg)
          STATE_RESET:
            begin
               state_next = STATE_IDLE;
            end
          STATE_IDLE:
            begin
               if (req)
                 state_next = STATE_BUSY;
            end
          STATE_BUSY:
            begin
               if (~req & ack)
                 state_next = STATE_IDLE;
            end
          default:  //unreachable
            begin
               state_next = STATE_RESET;
            end
        endcase // case (state_reg)
     end // always @ *

   //Protocol rules
   //==============
   //always @(posedge clk_i)
   always @ ($global_clock)
     if (~rst) //disable assertions and constraints in reset
       begin
          if (state_reg === STATE_RESET)
            begin
               //Bus interface must be initialized by reset
               //(Rule 3.00, Rule 3.20)
               assert (~tgt_cyc_o);
               assert (~tgt_stb_o);
            end // if (state_reg == STATE_RESET)

          if (state_reg === STATE_BUSY)
            begin
               //CYC_I must be is asserted throughout the bus cycle
               assert (tgt_cyc_o);
               //Only one termination signal may be asserted at a time
               //(Rule 3.45)
               assume (|{~|{tgt_ack_i, tgt_err_i           }, //onehot0
                         ~|{tgt_ack_i,            tgt_rty_i},
                         ~|{           tgt_err_i, tgt_rty_i}});
               //Keep bus signals stable after bus request has been accepted
               if (~ack)
                 begin
                    assert ($stable(tgt_we_o));   //write enable
                    assert ($stable(tgt_lock_o)); //uninterruptable bus cycle
                    assert ($stable(tgt_sel_o));  //write data selects
                    assert ($stable(tgt_adr_o));  //address bus
                    assert ($stable(tgt_tga_o));  //address tags
                    assert ($stable(tgt_tgc_o));  //bus cycle tags
                    if (tgt_we_o)
                      begin
                         assert ($stable(tgt_dat_o)); //write data bus
                         assert ($stable(tgt_tgd_o)); //write data tags
                      end // if (tgt_we_o)
                 end // if (~ack)
            end // if (state_reg == STATE_BUSY)
       end // if (~rst)

   //Fairness constraints
   //====================
   assume property (s_eventually (~tgt_stall_i));                       //STALL_I must be deasserted eventually
   assume property (s_eventually (ack));                                //acknowledge must be given eventually
   assume property (s_eventually (~rst && (state_reg === STATE_IDLE))); //acknowledge must be given eventually
   //always @(posedge clk_i)
   //  begin
   //     assume property (s_eventually (~tgt_stall_i));                       //STALL_I must be deasserted eventually
   //     assume property (s_eventually (ack));                                //acknowledge must be given eventually
   //     assume property (s_eventually (~rst && (state_reg === STATE_IDLE))); //acknowledge must be given eventually
   //  end

   //Liveness Assertions
   //===================
   assert property (s_eventually (&{tgt_cyc_o, tgt_stb_o}));            //bus must be requested eventually
   //always @(posedge clk_i)
   //  begin
   //     assert property (s_eventually (&{tgt_cyc_o, tgt_stb_o}));            //bus must be requested eventually
   //  end

   //Testbench status signals
   //==================
   assign tb_fsm_reset = (state_reg === STATE_RESET) ? 1'b1 : 1'b0;
   assign tb_fsm_idle  = (state_reg === STATE_IDLE)  ? 1'b1 : 1'b0;
   assign tb_fsm_busy  = (state_reg === STATE_BUSY)  ? 1'b1 : 1'b0;

endmodule // wb_tgt_mon
