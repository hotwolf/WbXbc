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
//#    frequency to a target, running at a lower frequency.                     #
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
//#                                                                             #
//#    Transaction timing:                                                      #
//#                                                                             #
//#                     :__   :__   :__   :__   :__   :__   :__   :__   :__     #
//#    itr_clk_i      __|  |__|  |__|  |__|  |__|  |__|  |__|  |__|  |__|  |__  #
//#                     :_____:     :_____:     :_____:     :_____:     :_____  #
//#    tgt_clk_i      __|     |_____|     |_____|     |_____|     |_____|       #
//#                     :     :     :     :     :     :     :     :     :       #
//#                     :     :     :  Registered requests  :     :     :       #
//#    request from     :_____:_____:_____:_____:     :_____:_____:_____:       #  
//#    initiator      --|___________|___________|-----|_________________|-----  # 
//#                     :stall:     :stall:     :     :stall:stall:     :       #  
//#    request to       :     :_____:     :_____:     :     :     :_____:       #  
//#    target         --:-----|_____|-----|_____|-----:-----:-----|_____|-----  #  
//#                     :     : reg :     : reg :     :     :     : reg :       #  
//#    response from    :     :     :_____:_____:_____:_____:     :     :_____  #  
//#    target         --:-----:-----|___________|___________|-----:-----|_____  #  
//#                     :     :     :     :     :     :     :     :     :       #  
//#    response to      :     :     :_ _ _:_____:_ _ _:_____:     :     :_ _ _  #  
//#    initiator      --:-----:-----|_ _ _|_____|_ _ _|_____|-----:-----|_ _ _  #  
//#                     :     :     :unreg: reg :unreg: reg :     :     :unreg  #
//#                     :     :     :     :     :     :     :     :     :       #
//#                     :     :     :     :     :     :     :     :     :       #
//#                     :     :     : Unegistered requests  :     :     :       #
//#    request from     :_____:_____:_____:_____:     :_____:     :     :       #  
//#    initiator      --|___________|___________|-----|_____|-----:-----:-----  # 
//#                     :stall:     :stall:     :     :     :     :     :       #  
//#    request to       :     :_____:     :_____:     :_____:     :     :       #  
//#    target         --:-----|_____|-----|_____|-----|_____|-----:-----:-----  #  
//#                     :     :unreg:     :unreg:     :unreg:     :     :       #  
//#    response from    :     :     :_____:_____:_____:_____:_____:_____:       #  
//#    target         --:-----:-----|___________|___________|___________|-----  #  
//#                     :     :     :     :     :     :     :     :     :       #  
//#    response to      :     :     :_ _ _:_____:_ _ _:_____:_ _ _:_____:       #  
//#    initiator      --:-----:-----|_ _ _|_____|_ _ _|_____|_ _ _|_____|-----  #  
//#                     :     :     :unreg: reg :unreg: reg :unreg: reg :       #
//#                     :     :     :     :     :     :     :     :     :       #
//#                                                                             #
//#    Bus requests from the initiator to the target may be reistered           #
//#    (parameter REG_ITR). Responses from the target to the initiator may be   #
//#    registered as well (parameter REG_TGT).                                  #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   August 3, 2018                                                            #
//#      - Initial release                                                      #
//#   October 8, 2018                                                           #
//#      - Updated parameter and signal naming                                  #
//###############################################################################
`default_nettype none

module WbXbc_decelerator
  #(parameter ADR_WIDTH   = 16, //width of the initiator address bus
    parameter DAT_WIDTH   = 16, //width of each initiator data bus
    parameter SEL_WIDTH   = 2,  //number of initiator write data select lines
    parameter TGA_WIDTH   = 1,  //number of propagated address tags
    parameter TGC_WIDTH   = 1,  //number of propagated cycle tags
    parameter TGRD_WIDTH  = 1,  //number of propagated read data tags
    parameter TGWD_WIDTH  = 1,  //number of propagated write data tags
    parameter REG_ITR     = 0,  //register initiator bus inputs (request signals)
    parameter REG_TGT     = 0)  //register target bus inputs (response signals)

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
    input  wire                          itr_lock_i,                          //uninterruptable bus cycle |
    input  wire [SEL_WIDTH-1:0]          itr_sel_i,                           //write data selects        | initiator
    input  wire [ADR_WIDTH-1:0]          itr_adr_i,                           //address bus               | to
    input  wire [DAT_WIDTH-1:0]          itr_dat_i,                           //write data bus            | target
    input  wire [TGA_WIDTH-1:0]          itr_tga_i,                           //address tags              |
    input  wire [TGC_WIDTH-1:0]          itr_tgc_i,                           //bus cycle tags            |
    input  wire [TGWD_WIDTH-1:0]         itr_tgd_i,                           //write data tags           +-
    output reg                           itr_ack_o,                           //bus cycle acknowledge     +-
    output reg                           itr_err_o,                           //error indicator           | target
    output reg                           itr_rty_o,                           //retry request             | to
    output reg                           itr_stall_o,                         //access delay              | initiator
    output reg  [DAT_WIDTH-1:0]          itr_dat_o,                           //read data bus             |
    output reg  [TGRD_WIDTH-1:0]         itr_tgd_o,                           //read data tags            +-

    //Target interfaces
    //-----------------
    output reg                           tgt_cyc_o,                           //bus cycle indicator       +-
    output reg                           tgt_stb_o,                           //access request            |
    output reg                           tgt_we_o,                            //write enable              |
    output reg                           tgt_lock_o,                          //uninterruptable bus cycle |
    output reg  [SEL_WIDTH-1:0]          tgt_sel_o,                           //write data selects        | initiator
    output reg  [ADR_WIDTH-1:0]          tgt_adr_o,                           //write data selects        | to
    output reg  [DAT_WIDTH-1:0]          tgt_dat_o,                           //write data bus            | target
    output reg  [TGA_WIDTH-1:0]          tgt_tga_o,                           //address tags              |
    output reg  [TGC_WIDTH-1:0]          tgt_tgc_o,                           //bus cycle tags            |
    output reg  [TGWD_WIDTH-1:0]         tgt_tgd_o,                           //write data tags           +-
    input  wire                          tgt_ack_i,                           //bus cycle acknowledge     +-
    input  wire                          tgt_err_i,                           //error indicator           | target
    input  wire                          tgt_rty_i,                           //retry request             | to
    input  wire                          tgt_stall_i,                         //access delay              | initiator
    input  wire [DAT_WIDTH-1:0]          tgt_dat_i,                           //read data bus             |
    input  wire [TGRD_WIDTH-1:0]         tgt_tgd_i);                          //read data tags            +-

   //Internal signals
   reg [1:0] 				 state_next;                          //next state
   reg 					 capture_request;                     //capture initiator request
   reg 					 capture_response;                    //capture target response

   //State variable
   reg  [1:0]                            state_reg;                           //state variable

   //Registered initiator request signals
   reg                                   itr_we_reg;                          //write enable              +-
   reg                                   itr_lock_reg;                        //uninterruptable bus cycle |
   reg  [SEL_WIDTH-1:0]                  itr_sel_reg;                         //write data selects        | initiator
   reg  [ADR_WIDTH-1:0]                  itr_adr_reg;                         //address bus               | to
   reg  [DAT_WIDTH-1:0]                  itr_dat_reg;                         //write data bus            | target
   reg  [TGA_WIDTH-1:0]                  itr_tga_reg;                         //address tags              |
   reg  [TGC_WIDTH-1:0]                  itr_tgc_reg;                         //bus cycle tags            |
   reg  [TGWD_WIDTH-1:0]                 itr_tgd_reg;                         //write data tags           +-
				         
   //Registered target response signals        
   reg                                   tgt_ack_reg;                         //bus cycle acknowledge     +-
   reg                                   tgt_err_reg;                         //error indicator           | target
   reg                                   tgt_rty_reg;                         //retry request             | to
   reg  [DAT_WIDTH-1:0]                  tgt_dat_reg;                         //read data bus             | initiator
   reg  [TGRD_WIDTH-1:0]                 tgt_tgd_reg;                         //read data tags            +-

   //Capture initiator request
   always @(posedge async_rst_i or posedge itr_clk_i)
     if(async_rst_i)                                                          //asynchronous reset
       begin
          itr_we_reg	<= 1'b0;                                              //write enable              +-
          itr_lock_reg	<= 1'b0;                                              //uninterruptable bus cycle |
          itr_sel_reg	<= {SEL_WIDTH{1'b0}};                                 //write data selects        | initiator
          itr_adr_reg	<= {ADR_WIDTH{1'b0}};                                 //address bus               | to
          itr_dat_reg	<= {DAT_WIDTH{1'b0}};                                 //write data bus            | target
          itr_tga_reg	<= {TGA_WIDTH{1'b0}};                                 //address tags              |
          itr_tgc_reg	<= {TGC_WIDTH{1'b0}};                                 //bus cycle tags            |
          itr_tgd_reg	<= {TGWD_WIDTH{1'b0}};                                //write data tags           +-
       end
     else if(sync_rst_i)                                                      //synchronous reset
       begin
         itr_we_reg	<= 1'b0;                                              //write enable              +-
          itr_lock_reg	<= 1'b0;                                              //uninterruptable bus cycle |
          itr_sel_reg	<= {SEL_WIDTH{1'b0}};                                 //write data selects        | initiator
          itr_adr_reg	<= {ADR_WIDTH{1'b0}};                                 //address bus               | to
          itr_dat_reg	<= {DAT_WIDTH{1'b0}};                                 //write data bus            | target
          itr_tga_reg	<= {TGA_WIDTH{1'b0}};                                 //address tags              |
          itr_tgc_reg	<= {TGC_WIDTH{1'b0}};                                 //bus cycle tags            |
          itr_tgd_reg	<= {TGWD_WIDTH{1'b0}};                                //write data tags           +-
       end
     else if (capture_request & |REG_ITR)
       begin
          itr_we_reg	<= itr_we_i;                                          //write enable              +-
          itr_lock_reg	<= itr_lock_i;                                        //uninterruptable bus cycle |
          itr_sel_reg	<= itr_sel_i;                                         //write data selects        | initiator
          itr_adr_reg	<= itr_adr_i;                                         //address bus               | to
          itr_dat_reg	<= itr_dat_i;                                         //write data bus            | target
          itr_tga_reg	<= itr_tga_i;                                         //address tags              |
          itr_tgc_reg	<= itr_tgc_i;                                         //bus cycle tags            |
          itr_tgd_reg	<= itr_tgd_i;                                         //write data tags           +-
       end

   //Capture target response
   always @(posedge async_rst_i or posedge itr_clk_i)
     if(async_rst_i)                                                          //asynchronous reset
       begin
	  tgt_ack_reg	<= 1'b0;                                              //bus cycle acknowledge     +-
	  tgt_err_reg	<= 1'b0;                                              //error indicator           | target
	  tgt_rty_reg	<= 1'b0;                                              //retry request             | to
	  tgt_dat_reg	<= {DAT_WIDTH{1'b0}};                                //read data bus             | initiator
	  tgt_tgd_reg	<= {TGRD_WIDTH{1'b0}};                                //read data tags            +-
       end
     else if(sync_rst_i)                                                      //synchronous reset
       begin
	  tgt_ack_reg	<= 1'b0;                                              //bus cycle acknowledge     +-
	  tgt_err_reg	<= 1'b0;                                              //error indicator           | target
	  tgt_rty_reg	<= 1'b0;                                              //retry request             | to
	  tgt_dat_reg	<= {DAT_WIDTH{1'b0}};                                //read data bus             | initiator
	  tgt_tgd_reg	<= {TGRD_WIDTH{1'b0}};                                //read data tags            +-
       end
     else if (capture_response & |REG_TGT)
       begin
	  tgt_ack_reg	<= tgt_ack_i;                                         //bus cycle acknowledge     +-
	  tgt_err_reg	<= tgt_err_i;                                         //error indicator           | target
	  tgt_rty_reg	<= tgt_rty_i;                                         //retry request             | to
	  tgt_dat_reg	<= tgt_dat_i;                                         //read data bus             | initiator
	  tgt_tgd_reg	<= tgt_tgd_i;                                         //read data tags            +-
       end

   //Connect target request signals
   always @*
     if(|REG_ITR)
       begin	
	  tgt_we_o   = itr_we_reg;                                            //write enable              +-
	  tgt_lock_o = itr_lock_reg;                                          //uninterruptable bus cycle |
	  tgt_sel_o  = itr_sel_reg;                                           //write data selects        | initiator
	  tgt_adr_o  = itr_adr_reg;                                           //write data selects        | to
	  tgt_dat_o  = itr_dat_reg;                                           //write data bus            | target
	  tgt_tga_o  = itr_tga_reg;                                           //address tags              |
	  tgt_tgc_o  = itr_tgc_reg;                                           //bus cycle tags            |
	  tgt_tgd_o  = itr_tgd_reg;                                           //write data tags           +-
       end // if (|REG_ITR)
     else
       begin	
	  tgt_we_o   = itr_we_i;                                              //write enable              |
	  tgt_lock_o = itr_lock_i;                                            //uninterruptable bus cycle |
	  tgt_sel_o  = itr_sel_i;                                             //write data selects        | initiator
	  tgt_adr_o  = itr_adr_i;                                             //write data selects        | to
	  tgt_dat_o  = itr_dat_i;                                             //write data bus            | target
	  tgt_tga_o  = itr_tga_i;                                             //address tags              |
	  tgt_tgc_o  = itr_tgc_i;                                             //bus cycle tags            |
	  tgt_tgd_o  = itr_tgd_i;                                             //write data tags           +-
       end // else: !if(|REG_ITR)
   
   //Connect initiator response signals
   always @*
     if(|REG_TGT)
       begin
	  itr_ack_o   = tgt_ack_reg;                                          //bus cycle acknowledge     +-
	  itr_err_o   = tgt_err_reg;                                          //error indicator           | target
	  itr_rty_o   = tgt_rty_reg;                                          //retry request             | to
	  itr_dat_o   = tgt_dat_reg;                                          //read data bus             | initiator
	  itr_tgd_o   = tgt_tgd_reg;                                          //read data tags            +-
       end
     else
       begin
	  itr_ack_o   = tgt_ack_i;                                            //bus cycle acknowledge     +-
	  itr_err_o   = tgt_err_i;                                            //error indicator           | target
	  itr_rty_o   = tgt_rty_i;                                            //retry request             | to
	  itr_dat_o   = tgt_dat_i;                                            //read data bus             | initiator
	  itr_tgd_o   = tgt_tgd_i;                                            //read data tags            +-
       end
      
   //Finite state machine
   parameter STATE_READY         = 2'b00;  //waiting for bus request (reset state)
   parameter STATE_REQ_CAPTURED  = 2'b10;  //initiator request captured(reset state)
   parameter STATE_RESP_PENDING  = 2'b01;  //waiting for bus acknowledge
   parameter STATE_RESP_CAPTURED = 2'b11;  //target response captured
   always @*
     begin
        //Default outputs
        state_next       = state_reg;                                         //remain in current state
	tgt_cyc_o        = itr_cyc_i;                                         //propagate bus cycle indicator     
	tgt_stb_o        = itr_stb_i;                                         //propagate access request          
	itr_stall_o      = tgt_stall_i;                                       //propagate access delay            
	capture_request  = 1'b0;                                              //don't capture initiator request
	capture_response = 1'b0;                                              //don't capture target response
	case (state_reg)
	  STATE_READY:
	    if (|REG_ITR)                                                     //registered requests
	      begin
	         tgt_cyc_o   = 1'b0;                                          //don't propagate bus cycle indicator    
	         tgt_stb_o   = 1'b0;                                          //don't propagate access request         
		 itr_stall_o = 1'b1;                                          //stall initiator
		 if (~itr2tgt_sync_i & itr_cyc_i & itr_stb_i & ~tgt_stall_i)  //bus request before initiator only clock event 
		   begin
		      state_next      = STATE_REQ_CAPTURED;                   //handle captured initiator request
		      capture_request = 1'b1;                                 //capture initiator request
		   end
	      end // if (|REG_ITR)
	    else                                                              //registered requests
	      begin
		 if (itr2tgt_sync_i)                                          //concurrent clock event next
		   begin
		      if (itr_cyc_i & itr_stb_i & ~tgt_stall_i)               //bus request before initiator only clock event 
			state_next    = STATE_RESP_PENDING;                   //handle captured initiator request
		   end
		 else
		   begin
		      itr_stall_o     = 1'b1;                                 //stall initiator
		   end
	      end // else: !if(|REG_ITR)
	  STATE_REQ_CAPTURED:
	    if (|REG_ITR)                                                     //registered requests
	      begin
	       //tgt_cyc_o   = 1'b1;                                          //request target bus    
	       //tgt_stb_o   = 1'b1;                                          //         
		 if (itr2tgt_sync_i & ~tgt_stall_o)                           //bus request before concurrent clock event
		   state_next      = STATE_RESP_PENDING;                      //target asccess initiated
	      end
	    else
	      begin
		 state_next = STATE_READY;                                    //unreachable
	      end
	  STATE_RESP_PENDING:
	    if (|REG_TGT)                                                     //registered responses
	      begin							      
		 if (itr_ack_o | itr_err_o | itr_rty_o)			      
		   begin						      
		      state_next      = STATE_RESP_CAPTURED;                  //handle captured initiator request
		      capture_response = 1'b1;                                //capture target response	
		   end
	      end							      
	    else                                                              //unregistered responses
	      if (|REG_ITR)                                                   //registered requests
		begin							      
	           tgt_cyc_o   = 1'b0;                                        //don't propagate bus cycle indicator    
	           tgt_stb_o   = 1'b0;                                        //don't propagate access request         
		   itr_stall_o = 1'b1;                                        //stall initiator
		   if (~itr2tgt_sync_i &                                      //bus request before initiator only clock event
		       itr_cyc_i & itr_stb_i & ~tgt_stall_o) 
		     begin
			state_next      = STATE_REQ_CAPTURED;                 //handle captured initiator request
			capture_request = 1'b1;                               //capture initiator request
		     end						      
		   else							      
		     begin						      
			state_next      = STATE_READY;                        //bus is idle
		     end						      
		end // if (|REG_ITR)					      
	      else                                                            //registered requests
		begin							      
		   if (itr2tgt_sync_i)                                        //concurrent clock event next
		     begin						      
			if (itr_cyc_i & itr_stb_i & ~tgt_stall_i)             //bus request before initiator only clock event 
			  state_next    = STATE_RESP_PENDING;                 //wait for bus acknowledge
		     end
		   else
		     begin
			state_next      = STATE_READY;                        //bus is idle
			itr_stall_o     = 1'b1;                               //stall initiator
		     end
		end // else: !if(|REG_ITR)
	  STATE_RESP_CAPTURED:
	    if (|REG_TGT)                                                     //registered requests
	      if (|REG_ITR)                                                   //registered requests
		begin							      
	           tgt_cyc_o   = 1'b0;                                        //don't propagate bus cycle indicator    
	           tgt_stb_o   = 1'b0;                                        //don't propagate access request         
		   itr_stall_o = 1'b1;                                        //stall initiator
		   capture_response = 1'b1;                                   //capture target response	
		   if (~itr2tgt_sync_i &                                      //bus request before initiator only clock event
		       itr_cyc_i & itr_stb_i & ~tgt_stall_o) 
		     begin
			state_next      = STATE_REQ_CAPTURED;                 //handle captured initiator request
			capture_request = 1'b1;                               //capture initiator request
		     end						      
		   else							      
		     begin						      
			state_next      = STATE_READY;                        //bus is idle
		     end						      
		end // if (|REG_ITR)					      
	      else                                                            //registered requests
		begin							      
		   if (itr2tgt_sync_i)                                        //concurrent clock event next
		     begin						      
			if (itr_cyc_i & itr_stb_i & ~tgt_stall_o)             //bus request before initiator only clock event 
			  state_next    = STATE_RESP_PENDING;                 //wait for bus acknowledge
		     end
		   else
		     begin
			state_next      = STATE_READY;                        //bus is idle
			itr_stall_o     = 1'b1;                               //stall initiator
		     end
		end // else: !if(|REG_ITR)
	endcase // case (state_reg)
     end // always @ *

   //State variable
   always @(posedge async_rst_i or posedge itr_clk_i)
     if (async_rst_i)                                                         //asynchronous reset
       state_reg <= STATE_READY;				              
     else if (sync_rst_i)                                                     //synchronous reset
       state_reg <= STATE_READY;				              
     else if(1)							              
       state_reg <= state_next;                                               //state transition

endmodule // WbXbc_decelerator
