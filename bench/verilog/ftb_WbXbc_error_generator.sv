//###############################################################################
//# WbXbc - Formal Testbench - Error Generator                                  #
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
//#    This is the the formal testbench for the WbXbc_error_generator           #
//#    component.                                                               #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   October 10, 2018                                                          #
//#      - Initial release                                                      #
//#   November 9, 2018                                                          #
//#      - Added define "FORMAL_K_INDUCT" to constraint reachable states for    #
//#        k-induction proofs                                                   #
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

module ftb_WbXbc_error_generator
   (//Clock and reset
    //---------------
    input wire                    clk_i,                 //module clock
    input wire                    async_rst_i,           //asynchronous reset
    input wire                    sync_rst_i,            //synchronous reset

    //Initiator interface
    //-------------------
    input wire                    itr_cyc_i,             //bus cycle indicator       +-
    input wire                    itr_stb_i,             //access request            |
    input wire                    itr_we_i,              //write enable              |
    input wire                    itr_lock_i,            //uninterruptable bus cycle |
    input wire [`SEL_WIDTH-1:0]   itr_sel_i,             //write data selects        | initiator
    input wire [`ADR_WIDTH-1:0]   itr_adr_i,             //address bus               | to
    input wire [`DAT_WIDTH-1:0]   itr_dat_i,             //write data bus            | target
    input wire [`TGA_WIDTH-1:0]   itr_tga_i,             //address tags              |
    input wire [`TGT_CNT-1:0]     itr_tga_tgtsel_i,      //target select tags        |
    input wire [`TGC_WIDTH-1:0]   itr_tgc_i,             //bus cycle tags            |
    input wire [`TGWD_WIDTH-1:0]  itr_tgd_i,             //write data tags           +-
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
    input wire                    tgt_ack_i,             //bus cycle acknowledge     +-
    input wire                    tgt_err_i,             //error indicator           | target
    input wire                    tgt_rty_i,             //retry request             | to
    input wire                    tgt_stall_i,           //access delay              | initiator
    input wire [`DAT_WIDTH-1:0]   tgt_dat_i,             //read data bus             |
    input wire [`TGRD_WIDTH-1:0]  tgt_tgd_i);            //read data tags            +-

   //DUT
   //===
   WbXbc_error_generator
     #(.TGT_CNT   (`TGT_CNT),                            //number of target addresses
       .ADR_WIDTH (`ADR_WIDTH),                          //width of the address bus
       .DAT_WIDTH (`DAT_WIDTH),                          //width of each data bus
       .SEL_WIDTH (`SEL_WIDTH),                          //number of data select lines
       .TGA_WIDTH (`TGA_WIDTH),                          //number of propagated address tags
       .TGC_WIDTH (`TGC_WIDTH),                          //number of propagated cycle tags
       .TGRD_WIDTH(`TGRD_WIDTH),                         //number of propagated read data tags
       .TGWD_WIDTH(`TGWD_WIDTH))                         //number of propagated write data tags
   DUT
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
      .itr_tga_i        (itr_tga_i),                     //address tags              |
      .itr_tga_tgtsel_i (itr_tga_tgtsel_i),              //target select tags        |
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
   wb_itr_mon
     #(.ADR_WIDTH (`ADR_WIDTH),                          //width of the address bus
       .DAT_WIDTH (`DAT_WIDTH),                          //width of each data bus
       .SEL_WIDTH (`SEL_WIDTH),                          //number of data select lines
       .TGA_WIDTH (`TGA_WIDTH + `TGT_CNT),               //number of propagated address tags
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
      .itr_tga_i        ({itr_tga_tgtsel_i, itr_tga_i}), //address tags              |
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
       .TGA_WIDTH (`TGA_WIDTH + `TGT_CNT),               //number of propagated address tags
       .TGC_WIDTH (`TGC_WIDTH),                          //number of propagated cycle tags
       .TGRD_WIDTH(`TGRD_WIDTH),                         //number of propagated read data tags
       .TGWD_WIDTH(`TGWD_WIDTH))                         //number of propagated write data tags
   wb_pass_through
     (//Assertion control
      //-----------------
      .pass_through_en (|itr_tga_tgtsel_i),

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
      .itr_tga_i        ({itr_tga_tgtsel_i, itr_tga_i}), //address tags              |
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
     .tb_fsm_reset      (wb_pass_through_fsm_reset),     //FSM in RESET state
     .tb_fsm_idle       (wb_pass_through_fsm_idle),      //FSM in IDLE state
     .tb_fsm_busy       (wb_pass_through_fsm_busy));     //FSM in BUSY state

   //Additional assertions
   //=====================

   //Abbreviations
   wire                  rst       = |{async_rst_i, sync_rst_i};            //reset
   wire                  req       = &{~itr_stall_o, itr_cyc_i, itr_stb_i}; //request
   wire                  no_tgt    = ~|{itr_tga_tgtsel_i};                  //no target
   wire                  inval_req = &{req, no_tgt};                        //invalid request
   wire                  val_req   = &{req, ~no_tgt};                       //valid request
   wire                  ack       = |{itr_ack_o, itr_err_o, itr_rty_o};    //acknowledge

   //State Machine
   //=============
    //                             inval_req     _______
   //                      +------------------->/       \
   //                      |                    | ERROR |
   //                      |  +-----------------\_______/
   //                      |  |   ~req & ack      ^  |
   //        _______      _|__v_                  |  |
   // rst   /       \    /      \        inval_req|  |val_req
   //  O--->| RESET |--->| IDLE |               & |  | &
   //       \_______/    \______/              ack|  |ack
   //                      ^  |                   |  |
   //                      |  |    val_req       _|__v_
   //                      |  +---------------->/      \
   //                      |                    | BUSY |
   //                      +--------------------\______/
   //                             ~req & ack
   //State encoding
   parameter STATE_RESET = 2'b00;
   parameter STATE_IDLE  = 2'b01;
   parameter STATE_BUSY  = 2'b10;
   parameter STATE_ERROR = 2'b11;
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
               if (val_req)
                 state_next = STATE_BUSY;
               if (inval_req)
                 state_next = STATE_ERROR;
            end
          STATE_BUSY:
            begin
               if (~req & ack)
                 state_next = STATE_IDLE;
               if (inval_req & ack)
                 state_next = STATE_ERROR;
            end
          STATE_ERROR:
            begin
               if (~req & ack)
                 state_next = STATE_IDLE;
               if (val_req & ack)
                 state_next = STATE_BUSY;
            end
        endcase // case (state_reg)
     end // always @ *

   //Error response rules
   //====================
   always @*
     begin
        //Get an error reponse one clock cycle after the request
        if (state_reg == STATE_ERROR)
          begin
             assert (itr_err_o);
          end // if (state_reg == STATE_ERROR)
        //Don't pass through invalid requests
        if (inval_req)
          begin
             assert (~&{tgt_cyc_o, tgt_stb_o});
          end // if (inval_req)
     end // always @*

   //Fairness constraints
   //====================
   //A legal request must occur eventually
   assume property (s_eventually (&{tgt_cyc_o, tgt_stb_o, |itr_tga_tgtsel_i}));

   //Liveness Assertions
   //===================

   //Monitor state assertions
   //========================
   wire tb_fsm_reset = (state_reg === STATE_RESET) ? 1'b1 : 1'b0;
   wire tb_fsm_idle  = (state_reg === STATE_IDLE)  ? 1'b1 : 1'b0;
   wire tb_fsm_busy  = (state_reg === STATE_BUSY)  ? 1'b1 : 1'b0;
   wire tb_fsm_error = (state_reg === STATE_ERROR) ? 1'b1 : 1'b0;

   always @*
     begin
        //Reset states must be aligned
        assert (&{tb_fsm_reset, wb_itr_mon_fsm_reset, wb_tgt_mon_fsm_reset, wb_pass_through_fsm_reset} |
               ~|{tb_fsm_reset, wb_itr_mon_fsm_reset, wb_tgt_mon_fsm_reset, wb_pass_through_fsm_reset});

        //Initiator side idle states must be aligned
        assert (&{tb_fsm_idle, wb_itr_mon_fsm_idle} |
               ~|{tb_fsm_idle, wb_itr_mon_fsm_idle});

        //Initiator side busy states must be aligned
        assert (&{wb_tgt_mon_fsm_idle, wb_pass_through_fsm_idle} |
               ~|{wb_tgt_mon_fsm_idle, wb_pass_through_fsm_idle});

        //If initiator bus is idle, target bus must be idle
        if (wb_itr_mon_fsm_idle)
        assert (wb_tgt_mon_fsm_idle);

        //Invalid accesses must not be propagated to the target side
        if (tb_fsm_busy)
          assert (&{wb_itr_mon_fsm_busy, wb_tgt_mon_fsm_busy, wb_pass_through_fsm_busy});
        else if (tb_fsm_error)
          assert (&{wb_itr_mon_fsm_busy, ~wb_tgt_mon_fsm_busy, ~wb_pass_through_fsm_busy});
        else
          assert (&{~wb_itr_mon_fsm_busy, ~wb_tgt_mon_fsm_busy, ~wb_pass_through_fsm_busy});
     end // always @*

   //Cover valid state transitions
   //=============================
   always @(posedge clk_i)
     begin
        cover (($past(state_reg) == STATE_IDLE)  && (state_reg == STATE_BUSY));  //IDLE  -> BUSY
        cover (($past(state_reg) == STATE_BUSY)  && (state_reg == STATE_IDLE));  //BUSY  -> IDLE
        cover (($past(state_reg) == STATE_IDLE)  && (state_reg == STATE_ERROR)); //IDLE  -> ERROR
        cover (($past(state_reg) == STATE_ERROR) && (state_reg == STATE_IDLE));  //ERROR -> IDLE
        cover (($past(state_reg) == STATE_BUSY)  && (state_reg == STATE_ERROR)); //BUSY  -> ERROR
        cover (($past(state_reg) == STATE_ERROR) && (state_reg == STATE_BUSY));  //ERROR -> BUSY
     end // always @ (posedge clk_i)

`ifdef FORMAL_K_INDUCT
   //Avoid unreachable states in k-induction proofs
   //==============================================
   always @*
     begin
        //Reset states must be aligned
        assume(&{tb_fsm_reset, wb_itr_mon_fsm_reset, wb_tgt_mon_fsm_reset, wb_pass_through_fsm_reset} |
              ~|{tb_fsm_reset, wb_itr_mon_fsm_reset, wb_tgt_mon_fsm_reset, wb_pass_through_fsm_reset});

        //Initiator side idle states must be aligned
        assume(&{tb_fsm_idle, wb_itr_mon_fsm_idle} |
              ~|{tb_fsm_idle, wb_itr_mon_fsm_idle});

        //Initiator side busy states must be aligned
        assume(&{wb_tgt_mon_fsm_idle, wb_pass_through_fsm_idle} |
              ~|{wb_tgt_mon_fsm_idle, wb_pass_through_fsm_idle});

        //If initiator bus is idle, target bus must be idle
        if (wb_itr_mon_fsm_idle)
        assume(wb_tgt_mon_fsm_idle);

        //Invalid accesses must not be propagated to the target side
        if (tb_fsm_busy)
          assume (&{wb_itr_mon_fsm_busy, wb_tgt_mon_fsm_busy, wb_pass_through_fsm_busy});
        else if (tb_fsm_error)
          assume (&{wb_itr_mon_fsm_busy, ~wb_tgt_mon_fsm_busy, ~wb_pass_through_fsm_busy});
        else
          assume (&{~wb_itr_mon_fsm_busy, ~wb_tgt_mon_fsm_busy, ~wb_pass_through_fsm_busy});
     end // always @*

   //Enforce a reachable state within the k-intervall
   //================================================
   parameter tcnt_max   = (`FORMAL_K_INDUCT/2)-1;
   integer   tcnt       = tcnt_max;
   wire      reachable_state = 1'b0;  //known set of reachable states

   always @(posedge clk_i)
     begin
        //Decrement step counter
        if (tcnt > tcnt_max)
          tcnt = tcnt_max;
        if (tcnt <= 0)
          tcnt = tcnt_max;

          tcnt = tcnt - 1;

        //Determine known reachable states
        reachable_state = rst; //reset
        if (tcnt < tcnt_max)
          reachable_state = reachable_state | ($past(req) & ack);//acknowledged request

        //Stop step counter at first known reachable state
        if (reachable_state)
          tcnt = 0;

        //Enforce reachable state
        if (tcnt == 0)
          assume(reachable_state);
     end // always @ ($global_clock)

`endif //  `ifdef FORMAL_KVAL

`endif //  `ifdef FORMAL

endmodule // ftb_WbXbc_error_generator
