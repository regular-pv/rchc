#!/usr/bin/env ruby
# Usage: ./benchmark.rb EXEC N FILE*
# Output a CSV file on the standard output with the execution times of EXEC for each given FILE over N runs.
# EXEC is the path to rchc.
# If no parameter is given, it will assume being run from the echc root directory and use every examples.
# The error output is used to print debug informations.
# The CSV file has the following output:
# filepath, mean time (s), time deviation (s), mean learning time (s), learning time deviation (s), mean teaching time (s), teaching time deviation (s)
require 'open3'

$rchc = ARGV[0]
$n = ARGV[1].to_i
$files = ARGV[2..-1]

if $rchc.nil? then
	$rchc = "cargo +nightly run --release --"
	$n = 10
	$files = [
		"even", "equal", "cmp",
		"make-list", "sort-insert",
		"sum01", "sum02",
		"toip01", "toip02", "toip03", "toip04", "toip05",
		"append-nil"
	].map { |name| "examples/#{name}.smt2" }
end

if $files.nil? then
	STDERR.puts "no file given."
	exit 1
end

if $n <= 0 then
	STDERR.puts "invalid run count"
	exit 1
end

def mean(values)
	m = 0.0
	values.each { |v| m += v }
	m / values.size
end

def deviation(values, mean)
	d = 0.0
	values.each { |v| d += (v-mean)**2 }
	Math.sqrt(d / values.size)
end

$files.each do |filepath|
	cmd = "#{$rchc} --learn-fast -b #{filepath}"

	STDERR.print "#{cmd}... "
	STDERR.flush

	time = []
	learning_time = []
	teaching_time = []

	$n.times do
		stdout, stderr, status = Open3.capture3(cmd)
		result = /time: (?<total>[0-9]+\.[0-9]+)s \((?<learning>[0-9]+\.[0-9]+)s learning, (?<teaching>[0-9]+\.[0-9]+)s teaching\)/.match(stdout)

		time << result[:total].to_f
		learning_time << result[:learning].to_f
		teaching_time << result[:teaching].to_f
	end

	mean_time = mean(time)
	devi_time = deviation(time, mean_time)
	mean_learning_time = mean(learning_time)
	devi_learning_time = deviation(learning_time, mean_learning_time)
	mean_teaching_time = mean(teaching_time)
	devi_teaching_time = deviation(teaching_time, mean_teaching_time)

	puts "#{filepath}, #{mean_time}, #{devi_time}, #{mean_learning_time}, #{devi_learning_time}, #{mean_teaching_time}, #{devi_teaching_time}"

	STDERR.puts "done."
end
