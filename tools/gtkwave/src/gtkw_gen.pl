#! /usr/bin/env perl
###############################################################################
# WbXbc - GTKWave Save File and STEMS File Generator                          #
###############################################################################
#    Copyright 2018 Dirk Heisswolf                                            #
#    This file is part of the WbXbc project.                                  #
#                                                                             #
#    WbXbc is free software: you can redistribute it and/or modify            #
#    it under the terms of the GNU General Public License as published by     #
#    the Free Software Foundation, either version 3 of the License, or        #
#    (at your option) any later version.                                      #
#                                                                             #
#    WbXbc is distributed in the hope that it will be useful,                 #
#    but WITHOUT ANY WARRANTY; without even the implied warranty of           #
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            #
#    GNU General Public License for more details.                             #
#                                                                             #
#    You should have received a copy of the GNU General Public License        #
#    along with WbXbc.  If not, see <http://www.gnu.org/licenses/>.           #
###############################################################################
# Description:                                                                #
#    This script generates an initial GTKW file to speed up debugging.        #
#                                                                             #
###############################################################################
# Version History:                                                            #
#   October 23, 2018                                                          #
#      - Initial release                                                      #
###############################################################################

#################
# Perl settings #
#################
use 5.005;
use FindBin qw($RealBin);
use lib "$RealBin/blib/arch";
use lib "$RealBin/blib/lib";
use lib "$RealBin";

use Getopt::Long;
use IO::File;

use Verilog::Netlist;
use Verilog::Netlist::Module;
use Verilog::Getopt;
use strict;

############################
# Parse Verilog parameters #
############################
my $vopt = new Verilog::Getopt(filename_expansion=>1);
@ARGV = $vopt->parameter(@ARGV);

###########
# Netlist #
###########
my $nl = new Verilog::Netlist (options => $vopt,
			       keep_comments => 1,
			       use_vars => 1);

##############
# Top module #
##############
my $top_mod_ref;

##############################
# Parse remaining parameters #
##############################
my $trace_name;
my $gtkw_name;
my $stems_name;
my @file_names = ();
my $top_mod_name;
my $ropt = Getopt::Long::Parser->new;
$ropt->configure("no_pass_through");
if (! $ropt->getoptions ("help"	        => \&help,
			 "trace=s"	=> \$trace_name,
			 "gtkw=s"	=> \$gtkw_name,
			 "stems=s"	=> \$stems_name,
			 "top=s"        => \$top_mod_name,
			 "<>"		=> \&files)) {
    die sprintf("Try %s -help\n", $0);
}  

parse_verilog();
generate_stems_file();
generate_gtkw_file();
    
exit (0);

#############
# Help text #
#############
sub help {
    printf("usage: %s -top <module> -trace <trace file> -gtkw <gtkw file> -stems <stems file> [verilog parser options]\n", $0);
    printf("       Supported verilog parser options:\n");    
    printf("            +libext+I<ext>+I<ext>...    libext (I<ext>)\n");
    printf("            +incdir+I<dir>              incdir (I<dir>)\n");
    printf("            +define+I<var>=I<value>     define (I<var>,I<value>)\n");
    printf("            +define+I<var>              define (I<var>,undef)\n");
    printf("            -F I<file>                  Parse parameters in file relatively\n");
    printf("            -f I<file>                  Parse parameters in file\n");
    printf("            -v I<file>                  library (I<file>)\n");
    printf("            -y I<dir>                   module_dir (I<dir>)\n");
    printf("            -DI<var>=I<value>           define (I<var>,I<value>)\n");
    printf("            -DI<var>                    define (I<var>,undef)\n");
    printf("            -UI<var>                    undefine (I<var>)\n");
    printf("            -II<dir>                    incdir (I<dir>)\n");
exit (1);
}

###############
# Input files #
###############
sub files {
    my $file = shift;
    push @file_names, "$file";
}

#################
# Parse verilog #
#################
sub parse_verilog {
    #Create new netlist
    #Read libraries
    $nl->read_libraries();

    #Read files
    foreach my $file_name (@file_names) {
	$nl->read_file (filename=>$file_name);
    }
    
    #Find top module
    if ($top_mod_name) {
	#Check given top module
	$top_mod_ref = $nl->find_module($top_mod_name) or die "Can't find $top_mod_name\n";
	$top_mod_ref->is_top(1);
    } else {
	#Find top module 
	foreach $top_mod_ref ($nl->modules) {
	    if ($top_mod_ref->is_top) {
		$top_mod_name = $top_mod_ref->name;
		last;
	    }
	} 
    }
    
    #Resolve references    
    $nl->link();
    $nl->lint();
    $nl->exit_if_error();
}

#######################
# Generate STEMS file #
#######################
sub generate_stems_file {
    
    #Only act if STEMS file is requested
    if ($stems_name) {
	my $out_handle = IO::File->new;
	$out_handle->open(">$stems_name") or die "Can't open $stems_name\n";

	#Parse hierarchy tree
	parse_stems($out_handle, $top_mod_ref);

	#close file
	$out_handle->close;
    }	
}

sub parse_stems {
    my $out_handle     = shift;
    my $parent_mod_ref = shift;

    #Obtain module information
    my $name       = $parent_mod_ref->name;
    my $file_name  = $parent_mod_ref->filename;
    my $first_line = $parent_mod_ref->lineno;
    #Determine last line of source code
    my $in_handle = IO::File->new;
    $in_handle->open("<$file_name") or die "Can't open $file_name\n";
    my $last_line = 0;
    while (my $line = <$in_handle>) {
	$last_line++;
    }
    $in_handle->close();
    
    #Write module definition to STMS file
    $out_handle->printf("++ module %s file %s lines %d - %d\n", $name,
			                                        $file_name,
		       	                                        $first_line,
			                                        $last_line);

    #Write signal definitions
    foreach my $net_ref ($parent_mod_ref->nets_sorted()) {
	if ($net_ref->decl_type ne "parameter") {
	    $out_handle->printf("++ var %s module %s\n", $net_ref->name,
	  			                         $name);
	    #printf("%s[%d:%d]\n", $net_ref->name, $net_ref->msb, $net_ref->lsb);
	}
   }

    #Write child relations
    my @cell_refs = $parent_mod_ref->cells_sorted();
    foreach my $cell_ref (@cell_refs) {
	my $inst_name = $cell_ref->name;
	my $mod_name  = $cell_ref->submodname;
	$out_handle->printf("++ comp %s type %s parent %s\n", $inst_name,
			                                      $mod_name,
			                                      $name);
    }
 
    #Parse children
    foreach my $cell_ref (@cell_refs) {
	my $mod_ref  = $cell_ref->submod;
	parse_stems($out_handle, $mod_ref);
    }
}

#######################
# Generate GTKW file #
#######################
sub generate_gtkw_file {
    #Time
    my $sec;
    my $min;
    my $hour;
    my $mday;
    my $mon;
    my $year;
    my $wday;
    my $yday;
    my $isdst;
    my @months = ("Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec");
    my @days   = ("Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat");
        
    #Only act if GTKW file is requested
    if ($gtkw_name) {
	my $out_handle = IO::File->new;
	$out_handle->open(">$gtkw_name") or die "Can't open $gtkw_name\n";

	#Print header
	($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime(time);
	$year += 1900;
        $out_handle->printf("[*]\n");
        $out_handle->printf("[*] WbXbc GTKW file generator\n");
        $out_handle->printf("[*] %3s, %3s %.2d %4d\n", $days[$wday], 
			                               $months[$mon], 
			                               $mday, 
			                               $year);
        $out_handle->printf("[*]\n");

	#Print trace file information
	#Only act if trace file is given
	if ($trace_name) {
	    my @stats = stat($trace_name);
	    my $mtime = $stats[9];
	    my $size  = $stats[7];
	    ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime($mtime);
	    $year += 1900;
            $out_handle->printf("[dumpfile] \"%s\"\n", $trace_name);
            #$out_handle->printf("[dumpfile_mtime] %3s %3s %.2d %.2d:%2d:%2d %4d\n", $days[$wday], 
            $out_handle->printf("[dumpfile_mtime] \"%3s %3s %.2d %.2d:%2d:%2d %4d\"\n", $days[$wday], 
				                                                        $months[$mon], 
				                                                        $mday, 
				                                                        $hour, 
				                                                        $min, 
				                                                        $sec, 
				                                                        $year);
            $out_handle->printf("[dumpfile_size] %d\n", $size);
	    if ($trace_name =~ /\.vcd$/) {
		$out_handle->printf("[optimize_vcd]\n");
	    }
	}

	#Print save file information
	$out_handle->printf("[savefile] \"%s\"\n", $gtkw_name);

	#Print window information
            $out_handle->printf("[timestart] 0\n");
            $out_handle->printf("[size] 1000 600\n");
            $out_handle->printf("[pos] -1 -1\n");
            $out_handle->printf("*-4.935745 6 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1\n");
            $out_handle->printf("[treeopen] %s.\n", $top_mod_name);
            $out_handle->printf("[sst_width] 210\n");
            $out_handle->printf("[signals_width] 150\n");
            $out_handle->printf("[sst_expanded] 1\n");
            $out_handle->printf("[sst_vpaned_height] 154\n");	

	#Add SYSCON signals
	add_group($out_handle,
		  "SYSCON",
		  $top_mod_ref,
		  $top_mod_name,
		  [["async_rst_i",0,0],
		   ["sync_rst_i",0,0],
		   ["clk_i",0,0],
		   ["itr_clk_i",0,0],
		   ["tgt_clk_i",0,0]],
		  1);

	#Add initiator busses

	#Add target busses

	#Add state machines    
	    
	#Print footer
        $out_handle->printf("[pattern_trace] 1\n");
        $out_handle->printf("[pattern_trace] 0\n");
	    
	$out_handle->close();
    }
}

sub add_group {
    my $out_handle  = shift;
    my $group_name  = shift;
    my $mod_ref     = shift;
    my $inst_name   = shift;
    my $net_list    = shift;
    my $is_open     = shift;

    my $net_cnt     = 0;
    my @net_out     = ();

    #check signals
    my $net_disp = "none"; 
    foreach my $net_entry (@$net_list) {
	my $net_name = $net_entry->[0];
	my $net_msb  = $net_entry->[1];
	my $net_lsb  = $net_entry->[2];
	#printf("--->%s[%d:%d]\n", $net_name, $net_msb, $net_lsb);
	#Check netnal name
	if (my $net_ref = $mod_ref->find_net($net_name)) {
	    #Fix out fo bound indexes
	    if ($net_msb > $net_ref->msb) {$net_msb = $net_ref->msb;}
	    if ($net_lsb > $net_ref->lsb) {$net_lsb = $net_ref->lsb;}
	    #printf("--->%s[%d:%d] found!\n", $net_name, $net_msb, $net_lsb);
	    #Include full bus range
	    if (($net_msb == $net_ref->msb) &&
		($net_lsb == $net_ref->lsb)) {
		#Single bit
		if (($net_msb == 0) &&
		    ($net_lsb == 0)) {
		    #Add display code
		    if ($net_disp ne "bit") {
			push(@net_out, "\@28");
			$net_disp = "bit";
		    }
		    push(@net_out, sprintf("%s.%s", $inst_name, $net_name));
		    #printf("---->%s\n", join("\n", @net_out));
		    $net_cnt++;
		} else {
		#Bus    
		    #Add display code
		    if ($net_disp ne "bus") {
			push(@net_out, "\@22");
			$net_disp = "bus";
		    }
		    push(@net_out, sprintf("%s.%s[%d:%d]", $inst_name, $net_name, $net_msb, $net_lsb));
		    $net_cnt++;
		}
	    } else { 
		#Include partial bus range
		#Add display code
		if ($net_disp ne "bus") {
		    push(@net_out, "\@22");
		    $net_disp = "bus";
		}
		my $alias_string = sprintf("#{%s.%s[%d:%d]}", $inst_name, $net_ref->name, $net_msb, $net_lsb);
		foreach my $i ($net_msb .. $net_lsb) {
		    $alias_string .= sprintf(" (%d)%s.%s[%d:%d]", (($net_ref->msb - $net_ref->lsb) - $i),
					                          $inst_name,
					                          $net_ref->name,
					                          $net_ref->msb,
					                          $net_ref->lsb);
		}
		push(@net_out, $alias_string);
		push(@net_out, "\@1001200");
		$net_cnt++;
	    }
	}
    }

    #printf("net_cnt: %d\n", $net_cnt);
    if ($net_cnt > 0) {
	#printf("net_cnt: %d\n", $net_cnt);
	#Add grout header
	$out_handle->printf("\@%s\n", $is_open ? "800200" : "");
	$out_handle->printf("-%s\n", $group_name);
	#Add signals
	foreach my $line (@net_out) {
	    $out_handle->print($line . "\n");
	}
	#Add grout footer
	$out_handle->printf("\@%s\n", $is_open ? "1000200" : "");
	$out_handle->printf("-%s\n", $group_name);
    }
}

1;
