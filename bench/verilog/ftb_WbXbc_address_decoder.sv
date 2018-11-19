//###############################################################################
//# WbXbc - Formal Testbench - Address Decoder                                  #
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
//#    This is the the formal testbench for the WbXbc_address_decoder           #
//#    component.                                                               #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   October 16, 2018                                                          #
//#      - Initial release                                                      #
//###############################################################################
`default_nettype none

//DUT configuration
//=================
//Default configuration
//---------------------
`ifndef CONF_DEFAULT
`endif

//Fall back
//---------
`ifndef TGT_CNT
`define TGT_CNT     4
`endif
`ifndef ADR_WIDTH
`define ADR_WIDTH   16
`endif
`ifndef DAT_WIDTH
`define DAT_WIDTH   16
`endif
`ifndef SEL_WIDTH
`define SEL_WIDTH   2
`endif
`ifndef TGA_WIDTH
`define TGA_WIDTH   1
`endif
`ifndef TGC_WIDTH
`define TGC_WIDTH   1
`endif
`ifndef TGRD_WIDTH
`define TGRD_WIDTH  1
`endif
`ifndef TGWD_WIDTH
`define TGWD_WIDTH  1
`endif

module ftb_WbXbc_address_decoder
   (//Clock and reset
    //---------------
    input wire                    clk_i,                 //module clock
    input wire                    async_rst_i,           //asynchronous reset
    input wire                    sync_rst_i,            //synchronous reset

    //Target address regions
    //----------------------
    input wire [(`TGT_CNT*`ADR_WIDTH)-1:0] region_adr_i, //target address
    input wire [(`TGT_CNT*`ADR_WIDTH)-1:0] region_msk_i, //selects relevant address bits

    //Initiator interface
    //-------------------
    input  wire                   itr_cyc_i,             //bus cycle indicator       +-
    input  wire                   itr_stb_i,             //access request            |
    input  wire                   itr_we_i,              //write enable              |
    input  wire                   itr_lock_i,            //uninterruptable bus cycle |
    input  wire [`SEL_WIDTH-1:0]  itr_sel_i,             //write data selects        | initiator
    input  wire [`ADR_WIDTH-1:0]  itr_adr_i,             //address bus               | to
    input  wire [`DAT_WIDTH-1:0]  itr_dat_i,             //write data bus            | target
    input  wire [`TGA_WIDTH-1:0]  itr_tga_i,             //address tags              |
    input  wire [`TGC_WIDTH-1:0]  itr_tgc_i,             //bus cycle tags            |
    input  wire [`TGWD_WIDTH-1:0] itr_tgd_i,             //write data tags           +-
    output wire                   itr_ack_o,             //bus cycle acknowledge     +-
    output wire                   itr_err_o,             //error indicator           | target
    output wire                   itr_rty_o,             //retry request             | to
    output wire                   itr_stall_o,           //access delay              | initiator
    output wire [`DAT_WIDTH-1:0]  itr_dat_o,             //read data bus             |
    output wire [`TGRD_WIDTH-1:0] itr_tgd_o,             //read data tags            +-

    //Target interface
    //----------------
    output wire                   tgt_cyc_o,             //bus cycle indicator       +-
    output wire                   tgt_stb_o,             //access request            |
    output wire                   tgt_we_o,              //write enable              |
    output wire                   tgt_lock_o,            //uninterruptable bus cycle |
    output wire [`SEL_WIDTH-1:0]  tgt_sel_o,             //write data selects        | initiator
    output wire [`ADR_WIDTH-1:0]  tgt_adr_o,             //write data selects        | to
    output wire [`DAT_WIDTH-1:0]  tgt_dat_o,             //write data bus            | target
    output wire [`TGA_WIDTH-1:0]  tgt_tga_o,             //address tags              |
    output wire [`TGT_CNT-1:0]    tgt_tga_tgtsel_o,      //target select tags        |
    output wire [`TGC_WIDTH-1:0]  tgt_tgc_o,             //bus cycle tags            |
    output wire [`TGWD_WIDTH-1:0] tgt_tgd_o,             //write data tags           +-
    input  wire                   tgt_ack_i,             //bus cycle acknowledge     +-
    input  wire                   tgt_err_i,             //error indicator           | target
    input  wire                   tgt_rty_i,             //retry request             | to
    input  wire                   tgt_stall_i,           //access delay              | initiator
    input  wire [`DAT_WIDTH-1:0]  tgt_dat_i,             //read data bus             |
    input  wire [`TGRD_WIDTH-1:0] tgt_tgd_i);            //read data tags            +-

   //DUT
   //===
   WbXbc_address_decoder
     #(.TGT_CNT   (`TGT_CNT),                            //number of target addresses
       .ADR_WIDTH (`ADR_WIDTH),                          //width of the address bus
       .DAT_WIDTH (`DAT_WIDTH),                          //width of each data bus
       .SEL_WIDTH (`SEL_WIDTH),                          //number of data select lines
       .TGA_WIDTH (`TGA_WIDTH),                          //number of propagated address tags
       .TGC_WIDTH (`TGC_WIDTH),                          //number of propagated cycle tags
       .TGRD_WIDTH(`TGRD_WIDTH),                         //number of propagated read data tags
       .TGWD_WIDTH(`TGWD_WIDTH))                         //number of propagated write data tags
   DUT
     (//Target address regions
      //----------------------
      .region_adr_i     (region_adr_i),                  //target address
      .region_msk_i     (region_msk_i),                  //selects relevant address bits

      //Initiator interface
      //-------------------
      .itr_cyc_i        (itr_cyc_i),                     //bus cycle indicator       +-
      .itr_stb_i        (itr_stb_i),                     //access request            |
      .itr_we_i         (itr_we_i),                      //write enable              |
      .itr_lock_i       (itr_lock_i),                    //uninterruptable bus cycle |
      .itr_sel_i        (itr_sel_i),                     //write data selects        | initiator
      .itr_adr_i        (itr_adr_i),                     //address bus               | to
      .itr_dat_i        (itr_dat_i),                     //write data bus            | target
      .itr_tga_i        (itr_tga_i),                     //address tags              |
      .itr_tgc_i        (itr_tgc_i),                     //bus cycle tags            |
      .itr_tgd_i        (itr_tgd_i),                     //write data tags           +-
      .itr_ack_o        (itr_ack_o),                     //bus cycle acknowledge     +-
      .itr_err_o        (itr_err_o),                     //error indicator           | target
      .itr_rty_o        (itr_rty_o),                     //retry request             | to
      .itr_stall_o      (itr_stall_o),                   //access delay              | initiator
      .itr_dat_o        (itr_dat_o),                     //read data bus             |
      .itr_tgd_o        (itr_tgd_o),                     //read data tags            +-

      //Target interface
      //----------------
      .tgt_cyc_o        (tgt_cyc_o),                     //bus cycle indicator       +-
      .tgt_stb_o        (tgt_stb_o),                     //access request            |
      .tgt_we_o         (tgt_we_o),                      //write enable              |
      .tgt_lock_o       (tgt_lock_o),                    //uninterruptable bus cycle |
      .tgt_sel_o        (tgt_sel_o),                     //write data selects        | initiator
      .tgt_adr_o        (tgt_adr_o),                     //write data selects        | to
      .tgt_dat_o        (tgt_dat_o),                     //write data bus            | target
      .tgt_tga_o        (tgt_tga_o),                     //address tags              |
      .tgt_tga_tgtsel_o (tgt_tga_tgtsel_o),              //target select tags        |
      .tgt_tgc_o        (tgt_tgc_o),                     //bus cycle tags            |
      .tgt_tgd_o        (tgt_tgd_o),                     //write data tags           +-
      .tgt_ack_i        (tgt_ack_i),                     //bus cycle acknowledge     +-
      .tgt_err_i        (tgt_err_i),                     //error indicator           | target
      .tgt_rty_i        (tgt_rty_i),                     //retry request             | to
      .tgt_stall_i      (tgt_stall_i),                   //access delay              | initiator
      .tgt_dat_i        (tgt_dat_i),                     //read data bus             |
      .tgt_tgd_i        (tgt_tgd_i));                    //read data tags            +-

`ifdef FORMAL
   //Testbench signals
   wire                 wb_itr_mon_fsm_reset;            //FSM in RESET
   wire                 wb_itr_mon_fsm_idle;             //FSM in IDLE
   wire                 wb_itr_mon_fsm_busy;             //FSM in BUSY
   wire                 wb_tgt_mon_fsm_reset;            //FSM in RESET
   wire                 wb_tgt_mon_fsm_idle;             //FSM in IDLE
   wire                 wb_tgt_mon_fsm_busy;             //FSM in BUSY
   wire                 wb_pass_through_fsm_reset;       //FSM in RESET
   wire                 wb_pass_through_fsm_idle;        //FSM in IDLE
   wire                 wb_pass_through_fsm_busy;        //FSM in READ or WRITE

   //Abbreviations
   wire                                    req = &{~itr_stall_o, itr_cyc_i, itr_stb_i}; //request

   //SYSCON constraints
   //===================
   wb_syscon wb_syscon
     (//Clock and reset
      //---------------
      .clk_i            (clk_i),                         //module clock
      .sync_i           (1'b1),                          //clock enable
      .async_rst_i      (async_rst_i),                   //asynchronous reset
      .sync_rst_i       (sync_rst_i),                    //synchronous reset
      .gated_clk_o      ());                             //gated clock

   //Protocol assertions
   //===================
   //Initiator interface
   wb_itr_mon
     #(.ADR_WIDTH (`ADR_WIDTH),                          //width of the address bus
       .DAT_WIDTH (`DAT_WIDTH),                          //width of each data bus
       .SEL_WIDTH (`SEL_WIDTH),                          //number of data select lines
       .TGA_WIDTH (`TGA_WIDTH+(2*`TGT_CNT*`ADR_WIDTH)),  //number of propagated address tags
       .TGC_WIDTH (`TGC_WIDTH),                          //number of propagated cycle tags
       .TGRD_WIDTH(`TGRD_WIDTH),                         //number of propagated read data tags
       .TGWD_WIDTH(`TGWD_WIDTH))                         //number of propagated write data tags
   wb_itr_mon
     (//Clock and reset
      //---------------
      .clk_i            (clk_i),                         //module clock
      .async_rst_i      (async_rst_i),                   //asynchronous reset
      .sync_rst_i       (sync_rst_i),                    //synchronous reset

      //Initiator interface
      //-------------------
      .itr_cyc_i        (itr_cyc_i),                     //bus cycle indicator       +-
      .itr_stb_i        (itr_stb_i),                     //access request            |
      .itr_we_i         (itr_we_i),                      //write enable              |
      .itr_lock_i       (itr_lock_i),                    //uninterruptable bus cycle |
      .itr_sel_i        (itr_sel_i),                     //write data selects        | initiator
      .itr_adr_i        (itr_adr_i),                     //address bus               | to
      .itr_dat_i        (itr_dat_i),                     //write data bus            | target
      .itr_tga_i        ({region_adr_i,                  //region descriptors must   |
                          region_msk_i,                  // have TGA_I timing        |
                          itr_tga_i}),                   //address tags              |
      .itr_tgc_i        (itr_tgc_i),                     //bus cycle tags            |
      .itr_tgd_i        (itr_tgd_i),                     //write data tags           +-
      .itr_ack_o        (itr_ack_o),                     //bus cycle acknowledge     +-
      .itr_err_o        (itr_err_o),                     //error indicator           | target
      .itr_rty_o        (itr_rty_o),                     //retry request             | to
      .itr_stall_o      (itr_stall_o),                   //access delay              | initiator
      .itr_dat_o        (itr_dat_o),                     //read data bus             |
      .itr_tgd_o        (itr_tgd_o),                     //read data tags            +-

     //Testbench status signals
     //------------------------
     .tb_fsm_reset      (wb_itr_mon_fsm_reset),          //FSM in RESET state
     .tb_fsm_idle       (wb_itr_mon_fsm_idle),           //FSM in IDLE state
     .tb_fsm_busy       (wb_itr_mon_fsm_busy));          //FSM in BUSY state

   //Target interface
   wb_tgt_mon
     #(.ADR_WIDTH (`ADR_WIDTH),                          //width of the address bus
       .DAT_WIDTH (`DAT_WIDTH),                          //width of each data bus
       .SEL_WIDTH (`SEL_WIDTH),                          //number of data select lines
       .TGA_WIDTH (`TGA_WIDTH + `TGT_CNT),               //number of propagated address tags
       .TGC_WIDTH (`TGC_WIDTH),                          //number of propagated cycle tags
       .TGRD_WIDTH(`TGRD_WIDTH),                         //number of propagated read data tags
       .TGWD_WIDTH(`TGWD_WIDTH))                         //number of propagated write data tags
   wb_tgt_mon
     (//Clock and reset
      //---------------
      .clk_i            (clk_i),                         //module clock
      .async_rst_i      (async_rst_i),                   //asynchronous reset
      .sync_rst_i       (sync_rst_i),                    //synchronous reset

      //Target interface
      //----------------
      .tgt_cyc_o        (tgt_cyc_o),                     //bus cycle indicator       +-
      .tgt_stb_o        (tgt_stb_o),                     //access request            |
      .tgt_we_o         (tgt_we_o),                      //write enable              |
      .tgt_lock_o       (tgt_lock_o),                    //uninterruptable bus cycle |
      .tgt_sel_o        (tgt_sel_o),                     //write data selects        | initiator
      .tgt_adr_o        (tgt_adr_o),                     //write data selects        | to
      .tgt_dat_o        (tgt_dat_o),                     //write data bus            | target
      .tgt_tga_o        ({tgt_tga_tgtsel_o, tgt_tga_o}), //address tags              |
      .tgt_tgc_o        (tgt_tgc_o),                     //bus cycle tags            |
      .tgt_tgd_o        (tgt_tgd_o),                     //write data tags           +-
      .tgt_ack_i        (tgt_ack_i),                     //bus cycle acknowledge     +-
      .tgt_err_i        (tgt_err_i),                     //error indicator           | target
      .tgt_rty_i        (tgt_rty_i),                     //retry request             | to
      .tgt_stall_i      (tgt_stall_i),                   //access delay              | initiator
      .tgt_dat_i        (tgt_dat_i),                     //read data bus             |
      .tgt_tgd_i        (tgt_tgd_i),                     //read data tags            +-

     //Testbench status signals
     //------------------------
     .tb_fsm_reset      (wb_tgt_mon_fsm_reset),          //FSM in RESET state
     .tb_fsm_idle       (wb_tgt_mon_fsm_idle),           //FSM in IDLE state
     .tb_fsm_busy       (wb_tgt_mon_fsm_busy));          //FSM in BUSY state

   //Pass-through assertions
   //=======================
   wb_pass_through
     #(.ADR_WIDTH (`ADR_WIDTH),                          //width of the address bus
       .DAT_WIDTH (`DAT_WIDTH),                          //width of each data bus
       .SEL_WIDTH (`SEL_WIDTH),                          //number of data select lines
       .TGA_WIDTH (`TGA_WIDTH),                          //number of propagated address tags
       .TGC_WIDTH (`TGC_WIDTH),                          //number of propagated cycle tags
       .TGRD_WIDTH(`TGRD_WIDTH),                         //number of propagated read data tags
       .TGWD_WIDTH(`TGWD_WIDTH))                         //number of propagated write data tags
   wb_pass_through
     (//Assertion control
      //-----------------
      .pass_through_en  (1'b1),

      //Clock and reset
      //---------------
      .clk_i            (clk_i),                         //module clock
      .async_rst_i      (async_rst_i),                   //asynchronous reset
      .sync_rst_i       (sync_rst_i),                    //synchronous reset

      //Initiator interface
      //-------------------
      .itr_cyc_i        (itr_cyc_i),                     //bus cycle indicator       +-
      .itr_stb_i        (itr_stb_i),                     //access request            |
      .itr_we_i         (itr_we_i),                      //write enable              |
      .itr_lock_i       (itr_lock_i),                    //uninterruptable bus cycle | initiator
      .itr_sel_i        (itr_sel_i),                     //write data selects        | initiator
      .itr_adr_i        (itr_adr_i),                     //address bus               | to
      .itr_dat_i        (itr_dat_i),                     //write data bus            | target
      .itr_tga_i        (itr_tga_i),                     //address tags              |
      .itr_tgc_i        (itr_tgc_i),                     //bus cycle tags            |
      .itr_tgd_i        (itr_tgd_i),                     //write data tags           +-
      .itr_ack_o        (itr_ack_o),                     //bus cycle acknowledge     +-
      .itr_err_o        (itr_err_o),                     //error indicator           | target
      .itr_rty_o        (itr_rty_o),                     //retry request             | to
      .itr_stall_o      (itr_stall_o),                   //access delay              | initiator
      .itr_dat_o        (itr_dat_o),                     //read data bus             |
      .itr_tgd_o        (itr_tgd_o),                     //read data tags            +-

      //Target interface
      //----------------
      .tgt_cyc_o        (tgt_cyc_o),                     //bus cycle indicator       +-
      .tgt_stb_o        (tgt_stb_o),                     //access request            |
      .tgt_we_o         (tgt_we_o),                      //write enable              |
      .tgt_lock_o       (tgt_lock_o),                    //uninterruptable bus cycle |
      .tgt_sel_o        (tgt_sel_o),                     //write data selects        | initiator
      .tgt_adr_o        (tgt_adr_o),                     //write data selects        | to
      .tgt_dat_o        (tgt_dat_o),                     //write data bus            | target
      .tgt_tga_o        (tgt_tga_o),                     //address tags              |
      .tgt_tgc_o        (tgt_tgc_o),                     //bus cycle tags            |
      .tgt_tgd_o        (tgt_tgd_o),                     //write data tags           +-
      .tgt_ack_i        (tgt_ack_i),                     //bus cycle acknowledge     +-
      .tgt_err_i        (tgt_err_i),                     //error indicator           | target
      .tgt_rty_i        (tgt_rty_i),                     //retry request             | to
      .tgt_stall_i      (tgt_stall_i),                   //access delay              | initiator
      .tgt_dat_i        (tgt_dat_i),                     //read data bus             |
      .tgt_tgd_i        (tgt_tgd_i),                     //read data tags            +-

     //Testbench status signals
     //------------------------
     .tb_fsm_reset      (wb_pass_through_fsm_reset),     //FSM in RESET state
     .tb_fsm_idle       (wb_pass_through_fsm_idle),      //FSM in IDLE state
     .tb_fsm_busy       (wb_pass_through_fsm_busy));     //FSM in BUSY state

   //Address region assertions
   //=========================
   integer         i, j, k, l;
   always @*
     begin
        //Address regions must not overlap
        for (i=1; i<`TGT_CNT; i=i+1)
        for (j=0; j<i; j=j+1)
          begin
             assume (|((region_adr_i[((i+1)*`ADR_WIDTH)-1:i*`ADR_WIDTH] ^
                        region_adr_i[((j+1)*`ADR_WIDTH)-1:j*`ADR_WIDTH]) &
                       (region_msk_i[((i+1)*`ADR_WIDTH)-1:i*`ADR_WIDTH]  &
                        region_msk_i[((j+1)*`ADR_WIDTH)-1:j*`ADR_WIDTH])));
          end // for (j=0; j<i; j=j+1)

        //Region select outputs must be "onehot0" encoded
        for (k=0; k<`TGT_CNT; k=k+1)
        for (l=0; l<`TGT_CNT; l=l+1)
        if (k != l)
          begin
             if (tgt_tga_tgtsel_o[k]) assert (~tgt_tga_tgtsel_o[l]);
          end
     end // always @ *

   //Monitor state assertions
   //========================
   always @*
     begin
        //Reset states must be aligned
        assert(&{wb_itr_mon_fsm_reset, wb_tgt_mon_fsm_reset, wb_pass_through_fsm_reset} |
              ~|{wb_itr_mon_fsm_reset, wb_tgt_mon_fsm_reset, wb_pass_through_fsm_reset});

        //Idle states must be aligned
        assert(&{wb_itr_mon_fsm_idle, wb_tgt_mon_fsm_idle, wb_pass_through_fsm_idle} |
              ~|{wb_itr_mon_fsm_idle, wb_tgt_mon_fsm_idle, wb_pass_through_fsm_idle});

        //Busy states must be aligned
       assert(&{wb_itr_mon_fsm_busy, wb_tgt_mon_fsm_busy, wb_pass_through_fsm_busy} |
              ~|{wb_itr_mon_fsm_busy, wb_tgt_mon_fsm_busy, wb_pass_through_fsm_busy});
     end // always @ *

   //Cover all target selects
   //========================
   integer   m;
   always @*
     begin
        for (m=0; m<`TGT_CNT; m=m+1)
          cover (req & tgt_tga_tgtsel_o[m]); //cover each target selection
        cover (req & ~|tgt_tga_tgtsel_o);    //cover empty target selection
     end // always @*

`endif //  `ifdef FORMAL

endmodule // ftb_WbXbc_address_decoder
