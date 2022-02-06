#!/usr/bin/raku

# ML regexes
my regex word { <alpha>\w*: };			my regex pstv { <[1..9]>\d*: };
my regex HEAD { \< <word><-[<>]>*: \> };
my regex AT { :r <-[<>]> | \<[ meta|link|input|img|hr|base ]>><-[>]>*\> };			# Asymetric tag/text content
my regex A { <AT>*: };
my regex CT { :r <AT> | \< (<word>)<-[<>]>* \> <~~>* '</' $0 \> };			# Content of node, its lazy mode repetition or none:
my regex C {<CT>*?};
			# Node optionally having content or direct head tag closing 
my regex ND {:r \< (<word>) [ <-[<>]>* \> <CT>* '</' $0 \> | <-[/<>]>* \/\> ] };

sub getNthEAtt ($tag, $nth, $srchspc, @ret, $nrev, $attg) {
	# If nth is backward, need get max nth +1 from which subtract it
	if $nrev {
		my $i=1;	$srchspc ~~ /^<HEAD> [ <C> [ \<$tag>>.+ & <ND> ] { ++$i } ]+/;
		return 1 if ($nth=$i-$nrev) < 1};
	return not $srchspc ~~ /^(<HEAD> [ <C> [ \<$tag>>$attg.+ & (<ND>) ] ]**{$nth} ) { @ret = [substr($0, 0, -$0.[0].chars), $1] }/
}

sub getAllEAtt ($tag, $search, $OFF, @ret, $nthrg, $att, $all) {
	my ($a, $b, $i, $off)= (1,'+');
	if $nthrg {
		my ($lt,$eq,$n)= ($nthrg ~~ / [ (\<) | \> ] (\=)? (.+)/ ).list;
		$b= $lt??	$eq?? "**$n" !! '**'~--$n !! ($a= $eq?? $n !! $n+1, $b) }
	return not $search ~~ /^
	(<HEAD>) { $OFF~=$0 }
	[ (<C>) [<?{ $all }> | <?before \<$tag>>$att> ] (<ND>)
	{ if ++$i>=$a {	push (@ret, [ $OFF~($off~=$1), $2 ] ); $off~=$2 }} ]$b /
}

# ML regex, Node counting max depth
my $MAX,my $DTH;
my regex M {:r \< (<word>) <-[<>]>* \> { $MAX=$DTH if ++$DTH>$MAX } [ <AT> | <~~> ]* '</' $0 \> {--$DTH} };
my regex N {{ $MAX=0 }<M>};

sub getAllDepth ($tag, $nth, $search, @ret, $OFF, $min, $nrev) {
	my (@nd, $offset,	$offs); my @curNode = [$OFF, $search];
	while @curNode {
		for @curNode -> $onref {
			if $nrev {	my $i=1;
				$onref[1] ~~ /^<HEAD> [ <C> [ \<$tag>>.+ & <ND> ] { ++$i } ]+/;	
				return 1 if ($nth=$i-$nrev) < 1}
			$onref[1] ~~ /^(<HEAD>) { $offset=$0 } [
			[ (<A>) { $offs=$offset~=$1 }
			[ <!before \<$tag>> > (<N>)
			{ push (@nd, [$onref[0].$offset, $2]) if $MAX > $min;	$offset~=$2 } ]? ]*:
			[ \<$tag>>.+ & (<N>) ]
			{ push (@nd, [$onref[0]~$offs, $3]) if $MAX > $min; $offset=$offs~$3 }
			] **{$nth}
			{ push (@ret, [$onref[0]~$offs, $3]) if $MAX >= $min }
			[ (<A>) { $offset~=$4 }
			(<N>) { push (@nd, [$onref[0]~$offset, $5]) if $MAX > $min; $offset~=$5 } ]* /
		}
		@curNode=@nd; @nd=();
	}
}

sub getAllDepNthRnAtt ($tag, $search, $OFF, @ret, $min, $nthrg, $att)	{			# in every nth or positon range 
	my ($onref, @nd, $offset, $M);
	my @curNode=[$OFF, $search];
	while @curNode {
		for @curNode -> $onref {
			my ($a,$b, $i)= (1, '+');
			if ($nthrg) {
				my ($lt, $e, $n)= ($nthrg~~ / [ (\<)| \> ] (\=)? (.+) /).list;
				$b = $lt??	$e?? "**$n" !! '**'~ --$n !! ($a=$e?? $n !! $n+1, $b)	}
			$onref[1] ~~ /:r ^(<HEAD>) {$offset=$0}
			[ (<A>) {$offset~=$1}
			[ <?before \<$tag>>$att {$M=1} >?
			(<N>) { if ($MAX >= $min) {
				push (@ret, [$onref[0]~$offset, $2]) if $M and ++$i>=$a;
				push (@nd, [$onref[0]~$offset, $2]) if $MAX > $min}
			$M=0; $offset~=$2 } ]? ]$b /
		}
		@curNode=@nd; @nd=();
	}
	return !@ret
}

sub getAllDepthAatt ($att, $search, $OFF, @ret, $min) {
	my ($onref, @nd, $offset, $M);
	my @curNode=[$OFF, $search];
	while @curNode {
		for @curNode -> $onref {
			$onref[1] ~~ /:r ^(<HEAD>) {$offset=$0}
			[ (<A>) {$offset~=$1}
			[ <?before \<\w+$att {$M=1} >?
			(<N>) { if ($MAX >= $min) {
				push (@ret, [$onref[0]~$offset, $2]) if $M;
				push (@nd, [$onref[0]~$offset, $2]) if $MAX>$min;
				$M=0}
			$offset~=$2 } ]? ]+ /
		}
		@curNode=@nd; @nd=();
	}
	return !@ret
}
# Above subs:
# $^a = searched el tag/att. Returns 1 on match failure, else 0 and offset & node pairs in the 4rd arg: $^d

my @res;
sub getE_Path_Rec {			#			path,  offset-node pair
	my ($AllDepth, $tag, $nth,$nrev,$range, $attg, $aatt, $allnode, $path) = ($^a ~~
	m{:r ^\/ (\/)? \/ [
	(<-[/@*[]>+) [ \[ [ ( <pstv> || 'last()-'(<pstv>) ) | 'position()' <!before \<1 > (<[<>]> \=?<pstv>) | \@ (<-[\]]>+ |\*) ] \] ]? | \@ (<word> <-[/]>* | \*) | (\*) ] (.*) }).list;
	$attg=$attg?? '\s+'~($attg eq '*' ?? '\S' !! $attg) !!'';	$aatt=$aatt?? '\s+'~($aatt eq '*'?? '\S' !! $aatt) !!'';

	for @($^b) {
		my @OffNode;
		if $AllDepth {
			my $depth=split /\//,$path;
			if $tag?? $nth??
					getAllDepth $tag, $nth, $_[1], @OffNode, $_[0], $depth, $nrev	# offset-node pair return is in @OffNode..
					!! getAllDepNthRnAtt $tag, $_[1], $_[0], @OffNode, $depth, $range, $attg
				!! getAllDepthAatt $aatt, $_[1], $_[0], @OffNode, $depth {
					LAST return !@res;			# if no next iteration (the current is the last) return with
					next }														# error code based on whether there's been a result or no 
		} elsif $nth {
			if getNthEAtt $tag, $nth, $_[1], @OffNode, $nrev, $attg {
				LAST return !@res;
				next }
			$(@OffNode[0])[0]=$_[0].$(@OffNode[0])[0];
		} else {
			if getAllEAtt $tag, $_[1], $_[0], @OffNode, $range, $attg, $allnode {
				LAST return !@res;
				next }
		}
		if $path	{
				my $R= getE_Path_Rec $path, @OffNode;							# ..to always propagate to the next
				LAST return $R;
		}	else {			push @res, @OffNode }
	}
	return
}

my ($whole, $trPath, @valid, $O, $CP);
if @*ARGS {
	$trPath=shift @*ARGS;
	$O=shift @*ARGS;
	$whole=(my $file=shift @*ARGS).IO.slurp;
}else {
	put "Element path is of Xpath form e.g:\n\thtml/body/div[1]//div[1]/div[2]\nmeans find in a given HTML or XML file, the second div tag element that is under the first\ndiv element anywhere under the first div element, under any body element,\nunder any html element.\n\nTo put multiply at once, put one after another delimited by ; or |";
	die "No any Xpath given\n" if ($trPath=prompt "\nPut element path: ") ~~ /^\s*$/;

	my regex ata {\@ [<word> [ \=<word> ]? | \*]};
	my regex path {:r \/\/? [ <word> [ \[ [ <pstv> | 'last()-'<pstv> | 'position()'<!before \<1> <[<>]>\=?<pstv> | <ata> ] \] ]? | <ata> ] };
	my regex xpath {:r [ <path> | \.\.? ] <path>* <[/\h]>*$ };

	$trPath ~~ s:g/\h//;
	for split /<[|;]>/, $trPath {
		if /<xpath>/ {
			if /^<-[/]>/ {
				if !$CP {
					print "\n'$_'\nis relative to a base/current path which is now empty";
					prompt "\n'$CP' is not a valid xpath" while ($CP = S:g/\s| \/+$ // with prompt "\nSpecify it:") !~~ <xpath>;
					$CP~~ s:g/\h | \/+$//
				}
				s/^'./' //;
				if /^'..'/ {	$CP~~ s/ \/?<-[/]>+:$//;	s/^..\/ // };
				$_="$CP/$_"
			}
			push @valid, $_;
		} else {
			my $y=prompt "'$_' is invalid Xpath\nSkip or abort it? (S: skip.  any else: abort) ";
			die "Aborting\n" unless $y~~ /:i ^s/
	}}
	my $file =  S/^\h+// with prompt "\nHTML/XML file name to process: ";
	"$file".IO ~~ :f or die "\n'$file' not exist\n";
	"$file".IO ~~ :r or die "\n'$file' is not readable\n";
	
	$whole="$file".IO.slurp or die "\nCannot open '$file' well\n";
	say "\nChecking HTML document '$file'... ";
}
die "can't parse it due to its ill-formed of HTML unbalanced tag pair\n" unless $whole ~~ /:r ^\s*
( [ '<?xml'>> <-[<>]>* \> \s* ]? '<!DOCTYPE' <-[>]>* \> <-[<]>*) ( \<(<alpha>\w*) <-[<>]>* \> <CT>* '</' $0 \>)/;
my @in= [ [$0, $1], ];
my $firsTAG= $1.[0];

my ($ER, @path, @fpath, @miss, @short);
for @valid.sort({ chars $^a <=> chars $^b}) {
	if $ER {
		say "\nSkip it to process the next path? (Y/Enter: yes. any else: Abort) ";
		(prompt) ~~ /:i ^[\h*y]?$/ or die "Aborting\n"
	}
	@res=();
	/^ \/(<word>)(\/.*) /;
#put "=*=$1\n=$_[0]\n=$_[1]" for @in;exit;
	if $0 ne $firsTAG or $ER =getE_Path_Rec $1, @in {
		push @miss, $_;
		print "\nCan't find '$_'"
	} else {
		push (@path, [$_, @res]);
		my $cur=$_;					# Optimize removal: filter out longer path whose head is the same as shorter one
		N: {
			last N if $cur ~~ /^"$_"/ for @short;
			push @fpath, @res
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
	when not /r|R/ {
		$whole='';
		for @path {
			$whole ~= "\n$_[0]:";
			$whole ~= "\n-------------\n$_[1]\n" for @$_[1]
		}
		$ttl='\nExtracted element nodes:\n';
		last
	}
	default {
		@fpath= @fpath.sort({ chars $^b[0] <=> chars $^a[0] });
		
		$whole~~ s/^ {$_[0]}{$_[1]}(.*) $ /$_[0]$0/	for @fpath;
		$ttl='\nRemoval result:\n'}
}

if $outf {
	spurt $outf,$whole, :exclusive or die "Cannot open or write '$outf'\n"
} else {
	say "$ttl$whole" }
