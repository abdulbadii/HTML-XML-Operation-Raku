#!/usr/bin/raku

# ML regexes
my regex word { <alpha>\w*: };			my regex pstv { <[1..9]>\d*: };
my regex HEAD { \< <word><-[<>]>*: \> };
my regex AT {:r <-[<>]> | \<[ meta|link|input|img|hr|base ]>><-[>]>*\> };			# Asymetric tag/text content
my regex A { <AT>*: };
my regex CT { :r <AT>| \< (<word>)<-[<>]>* \> <~~>* '</' $0 \> };			# Content of node. Its lazy mode repetition or none:
my regex C {<CT>*?};										# Node optionally having content or direct head tag closing: 
my regex ND {:r \< (<word>) [ <-[<>]>* \> <CT>* '</' $0 \> | <-[/<>]>* \/\> ] };

sub getNthEAtt ($tag, $nth, $srchspc, @ret, $nrev, $attg) {
	# If nth is backward, need get max nth +1 from which subtract nth
	if $nrev {
		my $i=1;	$srchspc~~ /^<HEAD> [ <C> [ \<$tag>>.+ & <ND> ] { ++$i } ]+/;
		return 1 if ($nth=$i-$nth) < 1}
	return not $srchspc~~ /^(<HEAD>[ <C> [ \<$tag>>$attg.+ & (<ND>) ] ]**{$nth} ) { @ret= ([substr($0, 0, -$0.[0].chars), $1],) }/
};

sub getAllEAtt ($tag, $search, $Off, @ret, $nth, $att, $all) {
	my ($a, $b, $offset, $off, $i)= (1,'+',$Off);
	if $nth {
		my ($lt,$eq,$n)= ($nth ~~ / [ (\<) | \> ] (\=)? (.+)/ ).list;
		$b= $lt??	$eq?? "**$n" !! '**'~--$n !! ($a= $eq?? $n !! $n+1, $b)}
	return not $search ~~ /^
	(<HEAD>) { $offset~=$0 }
	[ (<C>) [<?{ $all }> | <?before \<$tag>>$att> ] (<ND>)
	{ if ++$i>=$a { push @ret, ($offset~($off~=$1), $2) ; $off~=$2 }} ]{$b} /
}

# ML regex. Node counting max depth
my $MAX,my $DTH;
my regex M {:r \< (<word>) <-[<>]>* \> { $MAX=$DTH if ++$DTH>$MAX } [ <AT> | <~~> ]* '</' $0 \> {--$DTH} };
my regex N {{ $MAX=0 }<M>};

sub getAllDepth ($tag, $nth, $search, @ret, $OFF, $min, $nrev) {
	my (@nd, $offset,	$offs);
	my @curNode= ([$OFF, $search],);
	while @curNode {
		for @curNode -> $OffNode {
			if $nrev {
				my $i=1;	$OffNode[1] ~~ /^<HEAD> [ <C> [ \<$tag>>.+ & <ND> ] { ++$i } ]+/;	
				return 1 if ($nth=$i-$nth) < 1}
			$OffNode[1] ~~ /^(<HEAD>) { $offset=$0 }
			[ [ (<A>) { $offs=($offset~=$1) }
			[ <!before \<$tag>> > (<N>)
			{ push @nd, ($OffNode[0]~$offset, $2) if $MAX > $min;	$offset~=$2; } ]? ]*:
			[ \<$tag>>.+ & (<N>) ]
			{ push @nd, ($OffNode[0]~$offs, $3) if $MAX > $min; $offset=$offs~$3 }
			] **{$nth}
			{ push @ret, ($OffNode[0]~$offs, $3) if $MAX >= $min }
			[ (<A>) { $offset~=$4 }
			(<N>) { push @nd, ($OffNode[0]~$offset, $5) if $MAX > $min; $offset~=$5 } ]* /
		}
		@curNode=@nd; @nd=();
	}
	return !@ret
}

sub getAllDepNthRnAtt ($tag, $search, $OFF, @ret, $min, $nthrg, $att)	{			# in every nth or positon range 
	my (@nd, $offset, $M);
	my @curNode= ([$OFF, $search],);
	while @curNode {
		for @curNode -> $OffNode {
			my ($a,$b, $i)= (1, '+');
			if $nthrg {
				my ($lt, $e, $n)= ($nthrg~~ / [ (\<)| \> ] (\=)? (.+) /).list;
				$b = $lt??	$e?? "**$n" !! '**'~ --$n !! ($a=$e?? $n !! $n+1, $b)	}
			$OffNode[1] ~~ /:r ^(<HEAD>) {$offset=$0}
			[ (<A>) {$offset~=$1}
			[ <?before \<$tag>>$att {$M=1} >? (<N>)
			{ if ($MAX >= $min) {
				push @ret, ($OffNode[0]~$offset, $2) if $M and ++$i>=$a;
				push @nd, ($OffNode[0]~$offset, $2) if $MAX > $min}
			$M=0; $offset~=$2 } ]? ]{$b} /
		}
		@curNode=@nd; @nd=();
	}
	return !@ret
}

sub getAllDepthAatt ($att, $search, $OFF, @ret, $min) {
	my (@nd, $offset, $M);
	my @curNode= ([$OFF, $search],);
	while @curNode {
		for @curNode -> $OffNode {
			$OffNode[1] ~~ /:r ^(<HEAD>) {$offset=$0}
			[ (<A>) {$offset~=$1}
			[ <?before \<\w+$att {$M=1} >?
			(<N>) { if ($MAX >= $min) {
				push @ret, ($OffNode[0]~$offset, $2) if $M;
				push @nd, ($OffNode[0]~$offset, $2) if $MAX>$min;
				$M=0}
			$offset~=$2 } ]? ]+ /
		}
		@curNode=@nd; @nd=();
	}
	return !@ret
}
# Above subs: Returns 1 on match failure, else 0 and offset & node pairs in the 4rd arg: $^d

my @RES;
sub getE_Path_Rec {			#			path,  offset-node pair
	my ($AllDepth, $tag, $nthrev, $nth, $range, $attg, $aatt, $allnode, $path)= ($^a ~~
	/:r ^\/ (\/)? [
	(<-[/@*[]>+) [ \[ [ ('last()-')? $3=(<pstv>) | 'position()' <!before '<1'> $4=(<[<>]> \=?<pstv>) | \@ $5=(<-[\]]>+|\*) ] \] ]? | \@ $6=(<word> <-[/]>* | \*) | $7=(\*) ] $8=(.+)? /).list;
	
	for <nthrev nth range attg aatt allnode> {	$::($_)='' if !$::($_) }	# convert Mu type to Str one
	$attg=$attg?? '\s+'~($attg eq '*' ?? '\S' !! $attg) !! '';
	$aatt=$aatt?? '\s+'~($aatt eq '*'?? '\S' !! $aatt) !! '';
	for @$^b {
		my @OffNode;
		if $AllDepth {
			my $depth= 1+ (comb /\//,$path).Int;
			say "\nde=$depth=";
			if $tag?? $nth??
					getAllDepth $tag, $nth, $_[1], @OffNode, $_[0], $depth, $nthrev			# offset-node pair return is in @OffNode..
					!! getAllDepNthRnAtt $tag, $_[1], $_[0], @OffNode, $depth, $range, $attg
				!! getAllDepthAatt $aatt, $_[1], $_[0], @OffNode, $depth {
					LAST return !@RES;												# if no next iteration (current point is the last)
					next }																		# return error code based on whether there's been a result, error=0, or no (=1)
		} elsif $nth {
			if getNthEAtt $tag, $nth, $_[1], @OffNode, $nthrev, $attg {
				LAST return !@RES;
				next }
			$(@OffNode[0])[0]=$_[0]~$(@OffNode[0])[0];
		} else {
			if getAllEAtt $tag, $_[1], $_[0], @OffNode, $range, $attg, $allnode {
				LAST return !@RES;
				next }
		}
		if $path	{
				my $R= getE_Path_Rec $path, @OffNode;							# ...always propagate into the next
				LAST return $R
		}	else {			@RES.append: @OffNode }
	}
	return
}

my ($whole, $trPath, @valid, $O, $CP);
if @*ARGS {
	$trPath=shift @*ARGS;
	$O=shift @*ARGS;
	$whole=(my $file=shift @*ARGS).IO.slurp;
} else {
	put "Element path is of Xpath form e.g:\n\thtml/body/div[1]//div[1]/div[2]\nmeans find in a given HTML or XML file, the second div tag element that is under\nthe first div element anywhere under the first div element, under any body element,\nunder any html element.\n\nTo put multiply at once, put one after another delimited by ; or |";
	$trPath='/html/body//a[1]/span';
	#die "No any Xpath given\n" if ($trPath=prompt "\nPut element path: ") ~~ /^\s*$/;

	my regex ata {\@ [<word> [ \=<word> ]? | \*]};
	my regex path {:r \/\/? [ <word> [ \[ [<pstv> | 'last()-'<pstv> | 'position()'<!before \<1> <[<>]>\=?<pstv> | <ata>] \] ]? | <ata> ] };
	my regex xpath {:r ^\h* [ <path> | \.\.? ] <path>* <[/\h]>*$ };
	$trPath~~ s:g/\h+//;
	for split /<[|;]>/, $trPath {
		if /<xpath>/ {
			if /^<-[/]>/ {
				if !$CP {
					print "\n'$_'\nis relative to a base/current path which is now empty";
					prompt "\n'$CP' is not a valid xpath" while ($CP = S:g/\s| \/+$// with prompt "\nSpecify it:") !~~ <xpath>;
					$CP~~ s:g/\h | \/+$//
				}
				s/^ './' //;
				if /^ '..' / {	$CP~~ s/ \/?<-[/]>+:$//;	s/ ^'../' // };
				$_="$CP/$_"
			}
			push @valid, $_;
		} else {
			my $y=prompt "'$_' is invalid Xpath\nSkip or abort it? (S: skip.  any else: abort) ";
			die "Aborting\n" unless $y~~ /:i ^s/
	}}
	#my $file =  S/^\h+// with prompt "\nHTML/XML file name to process: ";
	"$file".IO ~~ :f or die "\n'$file' not exist\n";
	"$file".IO ~~ :r or die "\n'$file' is not readable\n";
	
	$whole="$file".IO.slurp or die "\nCannot open '$file' well\n";
	say "\nChecking HTML document '$file'... ";
}
die "can't parse it due to its ill-formed of HTML unbalanced tag pair\n" unless $whole~~ /:r
^\s*( [ '<?xml'>> <-[<>]>* \> \s* ]? '<!DOCTYPE' <-[>]>* \> <-[<]>*) ( \< (<alpha>\w*) <-[<>]>* \> <CT>* '</' $0 \>) /;
my @in= ([$0, $1],);
my $firsTAG= $1.[0];

my ($ER, @path, @fpath, @miss, @short);
for @valid.sort({ chars $^a <=> chars $^b}) {
	if $ER {
		say "\nSkip it to process the next path? (Y/Enter: yes. any else: Abort) ";
		(prompt) ~~ /:i ^[\h*y]?$/ or die "Aborting\n"
	}
	@RES=();
	/^ \/(<word>)(\/.*) /;
	if $0 ne $firsTAG or $ER= getE_Path_Rec $1, @in {
		push @miss, $_;
		print "\nCan't find '$_'"
	} else {
		push @path, ($_, @RES);
		my $cur=$_;					# Optimize removal: filter out longer path whose head is the same as shorter one
		N: {
			last N if $cur ~~ /^"$_"/ for @short;
			push @fpath, @RES
		}
		push @short, $_
	}
}

if @miss {
	if @path {
		print "\nKeep processing ones found? (Y/Enter: yes. any else: Abort) ";
		(S /^\h+// with prompt) ~~ /:i ^y?$/ or die "Aborting\n";
	} else { print "\n\nNothing was done";exit
}}
my $outf;
unless @*ARGS {
	$O = S/^\h*(\S)\h*/$0/ with prompt "\n\nWhich operation will be done :\n- Remove\n- Get\n(R: remove   Else key: get) ";
	print 'File name to save the result: (hit Enter to standard output) ';
	$outf = S/^\h+// with prompt;
}
if @path.end { print "\nProcessing the path:";print "\n$_[0]" for @path }

my $ttl;
given $O {
	when not /r|R/ {	$whole='';
		for @path {
			$whole ~= "\n$_[0]:";
			$whole ~= "\n-------------\n$_[1]\n" for @$_[1]
		}
		$ttl="\nExtracted element nodes:"
	}
	default {
		@fpath= @fpath.sort({ chars $^b[0] <=> chars $^a[0] });
		
		$whole~~ s/^ {$_[0]}{$_[1]}(.*) $ /$_[0]$0/	for @fpath;
		$ttl="\nThe Removal result:"}
}

if $outf {
	spurt $outf,$whole, :exclusive or die "Cannot open or write '$outf'\n"
} else {
	say "$ttl\n$whole" }
