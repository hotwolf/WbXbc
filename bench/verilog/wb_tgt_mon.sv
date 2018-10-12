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
//#    This set of assertion monitors a pipelined Wishbone initiator for        #
//#    protocol violations.                                                     #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   October 12, 2018                                                          #
//#      - Initial release                                                      #
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
    input  wire [TGRD_WIDTH-1:0]           tgt_tgd_i);       //read data tags            +-

   //Abbreviations
   wire                                    rst = |{async_rst_i, sync_rst_i};            //reset
   wire                                    req = &{~tgt_stall_i, tgt_cyc_o, tgt_stb_o}; //request
   wire                                    ack = |{tgt_ack_i, tgt_err_i, tgt_rty_i};    //acknowledge

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
   wire         [1:0]                           state_next;
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
   always @(posedge clk_i)
     begin
        if (state_reg == STATE_RESET)
          begin
             //Bus interface must be initialized by reset
             //(Rule 3.00, Rule 3.20)
             assert property (~tgt_cyc_o);
             assert property (~tgt_stb_o);
          end // if (state_reg == STATE_RESET)

        if (state_reg == STATE_IDLE)
          begin
             //Fairness -> a request must occur eventually
             assert property (s_eventually &{tgt_cyc_o, tgt_stb_o});
	     if (&{tgt_cyc_o, tgt_stb_o})
	       assume property (s_eventually ~tgt_stall_i); 
          end // if (state_reg == STATE_IDLE)

        if (state_reg == STATE_BUSY)
          begin
 	     //CYC_I must be is asserted throughout the bus cycle
	     assert property (tgt_cyc_o);
             //Fairness -> each bus cycle must be terminated
             //(Rule 3.35)
             assume property (s_eventually ack);
             //Only one termination signal may be asserted at a time
             //(Rule 3.45)
             assume property (|{~|{tgt_ack_i, tgt_err_i           }, //onehot0
                                ~|{tgt_ack_i,            tgt_rty_i},
                                ~|{           tgt_err_i, tgt_rty_i}});
	     //Keep bus signals stable after bus request has been accepted
	     if (~ack)
	       begin
	   	  assert property ($stable(tgt_lock_o)); //uninterruptable bus cycle
		  assert property ($stable(tgt_sel_o));  //write data selects       
		  assert property ($stable(tgt_adr_o));  //address bus              
		  assert property ($stable(tgt_dat_o));  //write data bus           
		  assert property ($stable(tgt_tga_o));  //address tags             
		  assert property ($stable(tgt_tgc_o));  //bus cycle tags           
		  assert property ($stable(tgt_tgd_o));  //write data tags          
	       end		  
          end // if (state_reg == STATE_BUSY)
     end

endmodule // wb_tgt_mon
