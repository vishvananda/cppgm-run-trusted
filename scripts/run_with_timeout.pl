#!/usr/bin/env perl

use strict;
use warnings;

use POSIX qw(WNOHANG setpgid);

sub usage
{
	die "Usage: run_with_timeout.pl --timeout-sec SEC [--label LABEL] -- command [args...]\n";
}

my $timeout_sec;
my $label = 'command';
while (@ARGV)
{
	my $arg = shift @ARGV;
	if ($arg eq '--')
	{
		last;
	}
	elsif ($arg eq '--timeout-sec')
	{
		usage() if !@ARGV;
		$timeout_sec = shift @ARGV;
	}
	elsif ($arg eq '--label')
	{
		usage() if !@ARGV;
		$label = shift @ARGV;
	}
	else
	{
		usage();
	}
}

usage() if !@ARGV;

if (!defined($timeout_sec) || $timeout_sec !~ m/^\d+$/ || $timeout_sec == 0)
{
	exec {$ARGV[0]} @ARGV;
	die "Unable to exec $ARGV[0]: $!\n";
}

my $pid = fork();
die "fork failed: $!\n" if !defined($pid);
if ($pid == 0)
{
	setpgid(0, 0);
	exec {$ARGV[0]} @ARGV;
	die "Unable to exec $ARGV[0]: $!\n";
}

setpgid($pid, $pid);
my $has_process_group = 1;

sub wait_for_child
{
	my ($pid, $timeout_ms) = @_;
	while ($timeout_ms > 0)
	{
		my $res = waitpid($pid, WNOHANG);
		return 1 if $res == $pid;
		return 0 if $res < 0;
		select(undef, undef, undef, 0.01);
		$timeout_ms -= 10;
	}
	return 0;
}

sub terminate_child
{
	my ($pid, $has_process_group) = @_;
	kill 'TERM', $pid;
	kill 'TERM', -$pid if $has_process_group;
	if (!wait_for_child($pid, 2000))
	{
		kill 'KILL', $pid;
		kill 'KILL', -$pid if $has_process_group;
		waitpid($pid, 0);
	}
}

$SIG{INT} = sub {
	terminate_child($pid, $has_process_group);
	exit 130;
};
$SIG{TERM} = sub {
	terminate_child($pid, $has_process_group);
	exit 143;
};

if (!wait_for_child($pid, $timeout_sec * 1000))
{
	print STDERR "ERROR: $label timed out after ${timeout_sec}s\n";
	print STDERR "Command:";
	for my $arg (@ARGV)
	{
		(my $escaped = $arg) =~ s/'/'\\''/g;
		print STDERR " '$escaped'";
	}
	print STDERR "\n";
	terminate_child($pid, $has_process_group);
	exit 124;
}

exit($? >> 8) if ($? & 127) == 0;
exit(128 + ($? & 127));
