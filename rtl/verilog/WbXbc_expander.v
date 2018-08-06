//###############################################################################
//# WbXbc - Wishbone Crossbar Components - Bus Width Expander                   #
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
//#    This module connects a pipelined Wishbone initiator to a target with     #
//#    wider data busses (twice the width of the initiator's data busses).      #
//#                                                                             #
//#                          +-------------------+                              #
//#                          |                   |                              #
//#                          |                   |                              #
//#             narrow       |       WbXbc       |      wide                    #
//#            initiator --->|      expander     |---> target                   #
//#               bus        |                   |      bus                     #
//#                          |                   |                              #
//#                          |                   |                              #
//#                          +-------------------+                              #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   July 30, 2018                                                             #
//#      - Initial release                                                      #
//###############################################################################
`default_nettype none

module WbXbc_expander
  #(parameter ITR_ADDR_WIDTH  = 16, //width of the initiator address bus
    parameter ITR_DATA_WIDTH  = 8,  //width of each initiator data bus
    parameter ITR_SEL_WIDTH   = 2,  //number of initiator write data select lines
    parameter TGA_WIDTH       = 1,  //number of propagated address tags
    parameter TGC_WIDTH       = 1,  //number of propagated cycle tags
    parameter TGRD_WIDTH      = 1,  //number of propagated read data tags
    parameter TGWD_WIDTH      = 1,  //number of propagated write data tags
    parameter BIG_ENDIAN      = 1)  //1=big endian, 0=little endian

   (//Clock and reset
    //---------------
    input wire                           clk_i,                               //module clock
    input wire                           async_rst_i,                         //asynchronous reset
    input wire                           sync_rst_i,                          //synchronous reset

    //Initiator interface
    //-------------------
    input  wire                          itr_cyc_i,                           //bus cycle indicator       +-
    input  wire                          itr_stb_i,                           //access request            |
    input  wire                          itr_we_i,                            //write enable              |
    input  wire                          itr_lock_i,                          //uninterruptable bus cycle | initiator
    input  wire [ITR_SEL_WIDTH-1:0]      itr_sel_i,                           //write data selects        | initiator
    input  wire [ITR_ADDR_WIDTH-1:0]     itr_adr_i,                           //address bus               | to
    input  wire [ITR_DATA_WIDTH-1:0]     itr_dat_i,                           //write data bus            | target
    input  wire [TGA_WIDTH-1:0]          itr_tga_i,                           //address tags              |
    input  wire [TGC_WIDTH-1:0]          itr_tgc_i,                           //bus cycle tags            |
    input  wire [TGWD_WIDTH-1:0]         itr_tgd_i,                           //write data tags           +-
    output wire                          itr_ack_o,                           //bus cycle acknowledge     +-
    output wire                          itr_err_o,                           //error indicator           | target
    output wire                          itr_rty_o,                           //retry request             | to
    output wire                          itr_stall_o,                         //access delay              | initiator
    output wire [ITR_DATA_WIDTH-1:0]     itr_dat_o,                           //read data bus             |
    output wire [TGRD_WIDTH-1:0]         itr_tgd_o,                           //read data tags            +-

    //Target interfaces
    //-----------------
    output wire                          tgt_cyc_o,                           //bus cycle indicator       +-
    output wire                          tgt_stb_o,                           //access request            |
    output wire                          tgt_we_o,                            //write enable              |
    output wire                          tgt_lock_o,                          //uninterruptable bus cycle |
    output wire [(ITR_SEL_WIDTH*2)-1:0]  tgt_sel_o,                           //write data selects        | initiator
    output wire [ITR_ADDR_WIDTH-2:0]     tgt_adr_o,                           //write data selects        | to
    output wire [(ITR_DATA_WIDTH*2)-1:0] tgt_dat_o,                           //write data bus            | target
    output wire [TGA_WIDTH-1:0]          tgt_tga_o,                           //address tags              |
    output wire [TGC_WIDTH-1:0]          tgt_tgc_o,                           //bus cycle tags            |
    output wire [TGWD_WIDTH-1:0]         tgt_tgd_o,                           //write data tags           +-
    input  wire                          tgt_ack_i,                           //bus cycle acknowledge     +-
    input  wire                          tgt_err_i,                           //error indicator           | target
    input  wire                          tgt_rty_i,                           //retry request             | to
    input  wire                          tgt_stall_i,                         //access delay              | initiator
    input  wire [(ITR_DATA_WIDTH*2)-1:0] tgt_dat_i,                           //read data bus             |
    input  wire [TGRD_WIDTH-1:0]         tgt_tgd_i);                          //read data tags            +-

   //Internal registers
   reg                                   itr_addr_0_reg;                       //LSB of the initiator address

   //Capture LSB of initiator address
   always @(posedge async_rst_i or posedge clk_i)
     if (async_rst_i)                                                         //asynchronous reset
       itr_addr_0_reg <= 1'b0;
     else if (sync_rst_i)                                                     //synchronous reset
       itr_addr_0_reg <= 1'b0;
     else if (itr_cyc_i   |                                                   //read access
              itr_stb_i   |
             ~itr_we_i    |
             ~tgt_stall_i)
       itr_addr_0_reg <= itr_adr_i[0];                                        //capture LSB of the initiator address

   //Signal propagation to the target bus
   assign tgt_cyc_o        = itr_cyc_i;                                       //bus cycle indicator       +-
   assign tgt_stb_o        = itr_stb_i;                                       //access request            |
   assign tgt_we_o         = itr_we_i;                                        //write enable              |
   assign tgt_lock_o       = itr_lock_i;                                      //uninterruptable bus cycle |
   assign tgt_sel_o        = (itr_adr_i[0] ^ |BIG_ENDIAN) ?                   //write data selects        |
                               {itr_sel_i, {ITR_SEL_WIDTH{1'b0}}} :           //                          | initiator
                               {{ITR_SEL_WIDTH{1'b0}}, itr_sel_i};            //                          | to
   assign tgt_adr_o        = itr_adr_i[ITR_ADDR_WIDTH-1:1];                   //write data selects        | target
   assign tgt_dat_o        = {itr_dat_i, itr_dat_i};                          //write data bus            |
   assign tgt_tga_o        = itr_tga_i;                                       //address tags              |
   assign tgt_tgc_o        = itr_tgc_i;                                       //bus cycle tags            |
   assign tgt_tgd_o        = itr_tgd_i;                                       //write data tags           +-

   //Signal propagation to the initiator bus
   assign itr_ack_o        = tgt_ack_i;                                       //bus cycle acknowledge     +-
   assign itr_err_o        = tgt_err_i;                                       //error indicator           |
   assign itr_rty_o        = tgt_rty_i;                                       //retry request             | target
   assign itr_stall_o      = tgt_stall_i;                                     //access delay              | to
   assign itr_dat_o        = (itr_addr_0_reg ^ |BIG_ENDIAN) ?                 //                          | initiator
                               tgt_dat_i[ITR_DATA_WIDTH-1:ITR_DATA_WIDTH/2] : //                          |
                               tgt_dat_i[(ITR_DATA_WIDTH/2)-1:0];             //                          |
   assign itr_tgd_o        = tgt_tgd_i;                                       //read data tags            +-

endmodule // WbXbc_expander
