//###############################################################################
//# WbXbc - Wishbone Initiator Monitor Assertions (Pipelined)                   #
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
//#    Wishbone initiator for protocol violations.                              #
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

module wb_itr_mon
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

    //Initiator interface
    //-------------------
    input  wire                            itr_cyc_i,        //bus cycle indicator       +-
    input  wire                            itr_stb_i,        //access request            |
    input  wire                            itr_we_i,         //write enable              |
    input  wire                            itr_lock_i,       //uninterruptable bus cycle | initiator
    input  wire [SEL_WIDTH-1:0]            itr_sel_i,        //write data selects        | to
    input  wire [ADR_WIDTH-1:0]            itr_adr_i,        //address bus               | target
    input  wire [DAT_WIDTH-1:0]            itr_dat_i,        //write data bus            |
    input  wire [TGA_WIDTH-1:0]            itr_tga_i,        //address tags              |
    input  wire [TGC_WIDTH-1:0]            itr_tgc_i,        //bus cycle tags            |
    input  wire [TGWD_WIDTH-1:0]           itr_tgd_i,        //write data tags           +-
    input  wire                            itr_ack_o,        //bus cycle acknowledge     +-
    input  wire                            itr_err_o,        //error indicator           | target
    input  wire                            itr_rty_o,        //retry request             | to
    input  wire                            itr_stall_o,      //access delay              | initiator
    input  wire [DAT_WIDTH-1:0]            itr_dat_o,        //read data bus             |
    input  wire [TGRD_WIDTH-1:0]           itr_tgd_o,        //read data tags            +-

    //Testbench status signals
    //------------------------
    output wire                            tb_fsm_reset,     //FSM in RESET state
    output wire                            tb_fsm_idle,      //FSM in IDLE state
    output wire                            tb_fsm_busy);     //FSM in BUSY state

   //Abbreviations
   wire                                    rst = |{async_rst_i, sync_rst_i};            //reset
   wire                                    req = &{~itr_stall_o, itr_cyc_i, itr_stb_i}; //request
   wire                                    ack = |{itr_ack_o, itr_err_o, itr_rty_o};    //acknowledge

   //Simplify counter examples (only toggle at clock events)
   //=======================================================
   always @($global_clock)
     if (!$rose(clk_i))
       begin
          assume ($stable(itr_cyc_i));              //bus cycle indicator
          assume ($stable(itr_stb_i));              //access request
          assume ($stable(itr_we_i));               //write enable
          assume ($stable(itr_lock_i));             //uninterruptable bus cycle
          assume ($stable(itr_sel_i));              //write data selects
          assume ($stable(itr_adr_i));              //address bus
          assume ($stable(itr_dat_i));              //write data bus
          assume ($stable(itr_tga_i));              //address tags
          assume ($stable(itr_tgc_i));              //bus cycle tags
          assume ($stable(itr_tgd_i));              //write data tags
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
   begin
      if (state_reg == STATE_RESET)
        begin
           //Bus interface must be initialized by reset
           //(Rule 3.00, Rule 3.20)
           assume (~itr_cyc_i);
           assume (~itr_stb_i);
        end // if (state_reg == STATE_RESET)

      if (~rst) //disable assertions and constraints in reset
        begin
           if (state_reg == STATE_BUSY)
             begin
                //CYC_I must be is asserted throughout the bus cycle
                assume (itr_cyc_i);
                //Only one termination signal may be asserted at a time
                //(Rule 3.45)
                assert (|{~|{itr_ack_o, itr_err_o           }, //onehot0
                          ~|{itr_ack_o,            itr_rty_o},
                          ~|{           itr_err_o, itr_rty_o}});
                //Keep bus signals stable after bus request has been accepted
                if (~ack)
                  begin
                     assume ($stable(itr_we_i));   //write enable
                     assume ($stable(itr_lock_i)); //uninterruptable bus cycle
                     assume ($stable(itr_sel_i));  //write data selects
                     assume ($stable(itr_adr_i));  //address bus
                     assume ($stable(itr_tga_i));  //address tags
                     assume ($stable(itr_tgc_i));  //bus cycle tags
                     if (itr_we_i)
                       begin
                          assume ($stable(itr_dat_i)); //write data bus
                          assume ($stable(itr_tgd_i)); //write data tags
                       end // if (itr_we_i)
                  end // if (~ack)
             end // if (state_reg == STATE_BUSY)
        end // if (~rst)
   end // always @ (posedge clk_i)

   //Fairness constraints
   //====================
   assume property (s_eventually (&{itr_cyc_i, itr_stb_i}));            //bus must be requested eventually
   assume property (s_eventually (~rst && (state_reg === STATE_IDLE))); //acknowledge must be given eventually
   //always @(posedge clk_i)
   //  begin
   //     assume property (s_eventually (&{itr_cyc_i, itr_stb_i}));            //bus must be requested eventually
   //     assume property (s_eventually (~rst && (state_reg === STATE_IDLE))); //acknowledge must be given eventually
   //  end

   //Liveness Assertions
   //===================
   assert property (s_eventually (~itr_stall_o));                       //STALL_I must be deasserted eventually
   assert property (s_eventually (ack));                                //acknowledge must be given eventually
   //always @(posedge clk_i)
   //  begin
   //     assert property (s_eventually (~itr_stall_o));                       //STALL_I must be deasserted eventually
   //     assert property (s_eventually (ack));                                //acknowledge must be given eventually
   //  end

   //Testbench status signals
   //==================
   assign tb_fsm_reset = (state_reg === STATE_RESET) ? 1'b1 : 1'b0;
   assign tb_fsm_idle  = (state_reg === STATE_IDLE)  ? 1'b1 : 1'b0;
   assign tb_fsm_busy  = (state_reg === STATE_BUSY)  ? 1'b1 : 1'b0;

endmodule // wb_itr_mon
