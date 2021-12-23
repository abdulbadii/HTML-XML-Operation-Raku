#!/usr/bin/perl -w
use strict;
# Pairs of offset & same-name elem returned in 4rd arg
sub getElem {	# $_[0]= searched elem tag  $_[1] = nth-1 $_[2]= whole elem to search
	 $_[2]=~ /\A(<(?>[a-z]\w*|!DOC)[^>]*+>(?:(?>(?'at'[^<>]|<(?>meta|link|input|img|hr|base)\b[^>]*+>)|(?'node'<(\w++)[^>]*+>(?>(?&at)|(?&node))*+<\/\g-1>))*?(?'tnode'(?=<$_[0]\b[^>]*+>)(?&node))){$_[1]}(?>(?&at)|(?&node))*?)((?&tnode))/;
	@{$_[3]}=[$1,$6];
	return
}

sub getEleMul {
	my ($off,$b)=$_[1]=~ /^(<(?>[a-z]\w*)[^>]*+>)(.*)/s;	my $pre='';
	while ($b=~/\G((?>(?'at'[^<>]|<(?>meta|link|input|img|hr|base)\b[^>]*+>)|(?'node'<(\w++)[^>]*+>(?>(?&at)|(?&node))*+<\/\g-1>))*?)((?=<$_[0]\b[^>]*+>)(?&node))/g) {
		push (@{$_[3]}, [$_[2].($off.=$pre.$1), $5]);
		$pre=$5
	}
	return
}

my @res;
sub getE_Path_Rec { my $iOffNode = $_[1];
	my ($tag,$nth,$path)=$_[0]=~ m#^/([^[/,]+)(?|\[(\d+|@[^]]+)\]|,(\d+))?(.*)#;
	print "$tag = $nth =$path=";
	my @OffNode;
	for (@$iOffNode) {
		print $_->[1];exit;

		if($nth) {
		print "\ns1= $tag  s2= $nth";
			&getElem($tag, $nth-1, $_->[1], \@OffNode);		# offset-node pair return is in @OffNode
			return 1 if !@OffNode;
			${$OffNode[0]}[0]=$_->[0].${$OffNode[0]}[0];
			if ($path) {
				&getE_Path_Rec( $path, \@OffNode )
			}else {
				push( @res, [@OffNode] )
			}
		}else {
		print "\ns1=$tag=\n****$_->[1]*=*=*"; #$_->[1]=======";
			&getEleMul($tag, $_->[1], $_->[0], \@OffNode );
			return 1 if !@OffNode;
			if ($path) {
				&getE_Path_Rec( $path, \@OffNode )
			}else {
				#print "\n$tag PUSH\n==@$_=="				for(@OffNode);
				push( @res, [@OffNode])
			}
		}

	}

	return
}

my ($whole, $trPath, @valid, $O, $CP);
if (@ARGV) {
	$trPath=shift;
	$O=shift;
	undef local $/;$whole=<>
}else {
	print "Element path is form of Xpath e.g: /html/body/div[1]/div[3]\n\n[1] may be replaced with ,1 e.g: html/body/div,1/div,3\nIt may be put multiply, delimited by ;\nFile name to work on: ";
	my $file='GuiTut.html';#*
	#my $file=<>=~s/^\h+//r=~ s/\s+$//r;#
	$!=1;-e $file or die "'$file' not exist\n";
	$!=2;open R,"$file" or die "Cannot open '$file'\n";
	print 'The element path(s): ';
	#$trPath='/html/body/main/div[1]/div[2]/div[1]/div[1]/p';
	$trPath='/html/body/nav[1]/div[1]/div/a';
	for (split(/;/,$trPath)) {#*
	#for (split(/;/,$trPath=<>)) {#
		L:if (m#^\s*/?/?([a-z]\w*+(?:\[(?>\d+|@[a-z]+(?:=\w+)?)\]|,\d+)?|@[a-z]\w*)(?://?(?1))*\s*$#i)	{
			s/\s|\/$//g;
			if (/^[^\/]/) {
			 if(!$CP) {
				print "\nRelativ path '$_'\nneeds the current path as base.";
				while(1){
					print " Put current path: "; $CP=<>=~s/\/$//r;
					last	if $CP=~m#^\s*(?:/html(?:/body)?)?(?:/[^/]+?(?:\[\d+\]|,\d+))++/?\s*$#;
					print "\nInvalid specified current path. Except 'html' or 'body' each node must have a nth number."
				}}
				$_="$CP/$_"
			}
			push (@valid, "$_"=~ s/\/$//r=~ s/,(\d+)/[$1]/gr);
		}else {
			print "'$_' is invalid Xpath\nEdit it or skip it? (E/Enter: Edit  S: Skip.  Else: Abort) ";my $y=<>;
			if($y=~/^e?$/i){
				print "Edit: ";$_=<>;goto L
			}elsif ($y=~/^s/i) {next
			}else{	die "Aborted by user\n"}
	}}
	undef local $/;$whole=<R>;close R;
}

my ($er, @path, @miss,$miss_);
for(@valid){
	if ($er) {
		print "\nSkip the missing '$miss_'\nto process the next path? (Y/Enter: yes. Else: aborting) ";
		<>=~/^(?:\h*y)?$/i or die "Aborted by user\n"}
	my @i=['',$whole];
	if ($er=&getE_Path_Rec($_=~s#(^/html|(?<=^/html/)body|(?<=^/html/body/)main)/#$1\[1\]/#gr, \@i)) {
		push(@miss,$miss_=$_)
	}else{
		push(@path, [$_, @res]);
	}
}
if ($er){
	print "\nCouldn't find ";
	if (@path){
		print "the last path\n'$miss_'\nKeep working on previous path(s) found? (Y/Enter: yes. Else: aborting) ";
		<>=~s/^\h+//r =~/^y?$/i or die "Aborted by user\n";
	}else{	die "'$miss_'\nNothing was done\n"}
}else{
		for(@miss){	print "Skipping non existant '$_'\n"}
}

# Removal, etc are optimized by filtering out path whose head is as the shorter one's
# First sort the path lengths
my @fpath=sort{length $a->[0] cmp length $b->[0]} @path;
P:for(my $i=1;$i<=$#fpath;) {
	for(my $j=0;$j<=$i-1;) {
		if ($fpath[$i]=~/^$fpath[$j++]/) {
			splice(@fpath,$i,1);
			next P}
	}
	$i++
}
unless	(@ARGV){
	print "\nWhich operation will be done :\n- Remove\n- Get\n(R: remove. Else: just get it) ";
	$O=<>=~s/^\h+//r=~ s/\s+$//r;
	print 'File name to save the result: (hit Enter to standard output) ';
	my $of=<>=~s/^\h+//r=~ s/\s+$//r;
	open W,">","$of" or die "Cannot open '$of'\n" if($of);
}
# Removal, etc must be from the longest elem offset found, first sort offset lengths descendingly
SW:
for ($O){
my @soffsetP=sort {length ${$b->[1]}[0] <=> ${$a->[1]}[0]} @fpath;
if (/^r/i){
	for(@soffsetP){
		$whole=~ s/\A(\Q${$_->[1]}[0]\E)\Q${$_->[1]}[1]\E(.*)\Z/$1$2/s}
	fileno W? print W $whole:print $whole;
	last SW;
}
my $o;
for (@path) {
	$o="$_->[0]:";
	$o.="\n==***$_->[1]***\n" for @{$_->[1]}
}
fileno W? print W $o:print $o;
}
close W;
