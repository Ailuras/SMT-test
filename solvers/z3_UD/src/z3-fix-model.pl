#!/usr/bin/env perl

$level = 0;
while (<>) {
    next if /^\s*;;.*/;
    if ($level == $skip_to_level) {
	# succesfully skipped
	$skip_to_level = -1;
    }
    if ($level == 1 &&
	/^\s*\((forall|declare-fun)/) {
	# skip this construct
	$skip_to_level = 1;
    }
    #    print "$level, $skip_to_level, $_";
    if ($skip_to_level < 0) {
        $_ =~ s/([a-zA-Z0-9]*)!val!([a-zA-Z0-9]*)/(as \@$2 $1)/g;
        print $_;
    }
    $paren = $_;
    $paren =~ tr/(//cd;
    $level += length($paren);
    $paren = $_;
    $paren =~ tr/)//cd;
    $level -= length($paren);
}   
