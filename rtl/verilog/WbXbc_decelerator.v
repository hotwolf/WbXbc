//###############################################################################
//# WbXbc - Wishbone Crossbar Components - Fast to Slow Bus Gasket              #
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
//#    along with Ninq1.  If not, see <http://www.gnu.org/licenses/>.           #
//###############################################################################
//# Description:                                                                #
//#    This module connects a pipelined Wishbone initiator, running at a higher #
//#    frequency to a target, running at a lower frequency:                     #
//#                                                                             #
//#                          +-------------------+                              #
//#                          |                   |                              #
//#                          |                   |                              #
//#              fast        |       WbXbc       |     slow                     #
//#            initiator --->|    decelerator    |---> target                   #
//#               bus        |                   |      bus                     #
//#                          |                   |                              #
//#                          |                   |                              #
//#                          +-------------------+                              #
//#                                                                             #
//#    Initiator and target clock must be synchrous to eachother. A clock sync  #
//#    signal must be available, indicating common clock edges:                 #
//#                                                                             #
//#                     :     :     :     :     :     :     :     :     :       #
//#                     :__   :__   :__   :__   :__   :__   :__   :__   :__     #
//#    itr_clk_i      __|  |__|  |__|  |__|  |__|  |__|  |__|  |__|  |__|  |__  #
//#                     :     :     :     :     :     :     :     :     :       #
//#                     :_____:     :_____:     :_____:     :_____:     :_____  #
//#    tgt_clk_i      __|     |_____|     |_____|     |_____|     |_____|       #
//#                     :     :     :     :     :     :     :     :     :       #
//#                     :     :     :     :     :     :     :     :     :       #
//#                     : _____     : _____     : _____     : _____     : ____  #
//#    itr2tgt_sync_i ___/     \_____/     \_____/     \_____/     \_____/      #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   August 3, 2018                                                            #
//#      - Initial release                                                      #
//###############################################################################
`default_nettype none

module WbXbc_decelerator
  #(parameter ADDR_WIDTH  = 16, //width of the initiator address bus
    parameter DATA_WIDTH  = 16, //width of each initiator data bus
    parameter SEL_WIDTH   = 2,  //number of initiator write data select lines
    parameter TGA_WIDTH   = 1,  //number of propagated address tags
    parameter TGC_WIDTH   = 1,  //number of propagated cycle tags
    parameter TGRD_WIDTH  = 1,  //number of propagated read data tags
    parameter TGWD_WIDTH  = 1)  //number of propagated write data tags

   (//Clock and reset
    //---------------
    input wire                           itr_clk_i,                           //initiator clock
    input wire                           itr2tgt_sync_i,                      //clock sync signal
    input wire                           async_rst_i,                         //asynchronous reset
    input wire                           sync_rst_i,                          //synchronous reset

    //Initiator interface
    //-------------------
    input  wire                          itr_cyc_i,                           //bus cycle indicator       +-
    input  wire                          itr_stb_i,                           //access request            |
    input  wire                          itr_we_i,                            //write enable              |
    input  wire                          itr_lock_i,                          //uninterruptable bus cycle | initiator
    input  wire [SEL_WIDTH-1:0]          itr_sel_i,                           //write data selects        | initiator
    input  wire [ADDR_WIDTH-1:0]         itr_adr_i,                           //address bus               | to
    input  wire [DATA_WIDTH-1:0]         itr_dat_i,                           //write data bus            | target
    input  wire [TGA_WIDTH-1:0]          itr_tga_i,                           //address tags              |
    input  wire [TGC_WIDTH-1:0]          itr_tgc_i,                           //bus cycle tags            |
    input  wire [TGWD_WIDTH-1:0]         itr_tgd_i,                           //write data tags           +-
    output wire                          itr_ack_o,                           //bus cycle acknowledge     +-
    output wire                          itr_err_o,                           //error indicator           | target
    output wire                          itr_rty_o,                           //retry request             | to
    output wire                          itr_stall_o,                         //access delay              | initiator
    output wire [DATA_WIDTH-1:0]         itr_dat_o,                           //read data bus             |
    output wire [TGRD_WIDTH-1:0]         itr_tgd_o,                           //read data tags            +-

    //Target interfaces
    //-----------------
    output wire                          tgt_cyc_o,                           //bus cycle indicator       +-
    output wire                          tgt_stb_o,                           //access request            |
    output wire                          tgt_we_o,                            //write enable              |
    output wire                          tgt_lock_o,                          //uninterruptable bus cycle |
    output wire [SEL_WIDTH-1:0]          tgt_sel_o,                           //write data selects        | initiator
    output wire [ADDR_WIDTH-1:0]         tgt_adr_o,                           //write data selects        | to
    output wire [DATA_WIDTH-1:0]         tgt_dat_o,                           //write data bus            | target
    output wire [TGA_WIDTH-1:0]          tgt_tga_o,                           //address tags              |
    output wire [TGC_WIDTH-1:0]          tgt_tgc_o,                           //bus cycle tags            |
    output wire [TGWD_WIDTH-1:0]         tgt_tgd_o,                           //write data tags           +-
    input  wire                          tgt_ack_i,                           //bus cycle acknowledge     +-
    input  wire                          tgt_err_i,                           //error indicator           | target
    input  wire                          tgt_rty_i,                           //retry request             | to
    input  wire                          tgt_stall_i,                         //access delay              | initiator
    input  wire [DATA_WIDTH-1:0]         tgt_dat_i,                           //read data bus             |
    input  wire [TGRD_WIDTH-1:0]         tgt_tgd_i);                          //read data tags            +-

   //Signal propagation to the target bus
   assign tgt_cyc_o        = itr_cyc_i;                                       //bus cycle indicator       +-
   assign tgt_stb_o        = itr_stb_i;                                       //access request            |
   assign tgt_we_o         = itr_we_i;                                        //write enable              |
   assign tgt_lock_o       = itr_lock_i;                                      //uninterruptable bus cycle | initiator
   assign tgt_sel_o        = itr_sel_i;                                       //write data selects        | to
   assign tgt_adr_o        = itr_adr_i;                                       //write data selects        | target
   assign tgt_dat_o        = itr_dat_i;                                       //write data bus            |
   assign tgt_tga_o        = itr_tga_i;                                       //address tags              |
   assign tgt_tgc_o        = itr_tgc_i;                                       //bus cycle tags            |
   assign tgt_tgd_o        = itr_tgd_i;                                       //write data tags           +-

   //Signal propagation to the initiator bus
   assign itr_ack_o        = ~itr2tgt_sync_i & tgt_ack_i;                     //bus cycle acknowledge     +-
   assign itr_err_o        = ~itr2tgt_sync_i & tgt_err_i;                     //error indicator           | target
   assign itr_rty_o        = ~itr2tgt_sync_i & tgt_rty_i;                     //retry request             | to
   assign itr_stall_o      = ~itr2tgt_sync_i | tgt_stall_i;                   //access delay              | initiator
   assign itr_dat_o        = tgt_dat_i;                                       //                          |
   assign itr_tgd_o        = tgt_tgd_i;                                       //read data tags            +-

endmodule // WbXbc_decelerator
