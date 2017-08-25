

for fullfile in $(find . -name "*.out");  do

rm $fullfile

done

for fullfile in $(find . -name "*.err");  do

rm $fullfile

done

for fullfile in $(find . -name "*.time");  do

rm $fullfile

done

