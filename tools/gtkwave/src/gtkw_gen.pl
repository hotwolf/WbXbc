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
use Pod::Usage;

use Verilog::Netlist;
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
			       use_vars => 0);

##############################
# Parse remaining parameters #
##############################
my $trace_name = '';
my $gtkw_name  = '';
my $stems_name = '';
my @file_names = ();
my $top_name   = '';
my $ropt = Getopt::Long::Parser->new;
$ropt->configure("no_pass_through");
if (! $ropt->getoptions ("debug"	=> \&debug,
			 "help"	        => \&help,
			 "trace=s"	=> \$trace_name,
			 "gtkw=s"	=> \$gtkw_name,
			 "stems=s"	=> \$stems_name,
			 "top=s"        => \$top_name,
			 "<>"		=> \&files)) {
    die sprintf("Try %s -help\n", $0);
}  

parse_verilog();
generate_stems_file();
generate_gtkw_file();
    
exit (0);

#########
# Debug #
#########
sub debug {
}

#############
# Help text #
#############
sub help {
    printf("usage: %s [verilog parser options] -trace <trace file> -gtkw <gtkw file> -stems <stems file>\n", $0);
    printf("       Supported verilog parser option:\n");    
    printf("            +libext+I<ext>+I<ext>...    libext (I<ext>)\n");
    printf("            +incdir+I<dir>              incdir (I<dir>)\n");
    printf("            +define+I<var>=I<value>     define (I<var>,I<value>)\n");
    printf("            +define+I<var>              define (I<var>,undef)\n");
    printf("            -F I<file>                  Parse parameters in file relatively\n");
    printf("            -f I<file>                  Parse parameters in file\n");
    printf("            -v I<file>                  library (I<file>)\n");
    printf("            -y I<dir>                   module_dir (I<dir>)\n");
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

    #Resolve references    
    $nl->link();
    $nl->lint();
    $nl->exit_if_error();
}

#######################
# Generate STEMS file #
#######################
sub generate_stems_file {
    my $top_mod
    
    #Only act if STEMS file is requested
    if ($stems_file) {
	my $out_handle = IO::File->new;
	$out_handle->open(">$stems_file") or die "Can't open $stems_file\n";

	#Find top module
	if ($top_name) {
	    #Check given top module
	    $top_mod = find_module($top_name) or die "Can't find $top_name\n";
	    $top_mod->is_top(1);
	} else {
	    #Find top module 
	    foreach $top_mod ($nl->modules) {
		if ($top_mod->is_top) {
		    break;
		}
	    } 
	}
	#Parse hierarchy tree
	parse_stems($out_handle, $top_mod);

	#close file
	$out_handle->close;
    }	
}




#######################
# Generate GTKW file #
#######################
sub generate_gtkw_file {


}

    


1;
