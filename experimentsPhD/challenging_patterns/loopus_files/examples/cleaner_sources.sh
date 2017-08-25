

for fullfile in $(find . -name "*.c");  do

rm $fullfile

done

for fullfile in $(find . -name "*.koat");  do

rm $fullfile

done

for fullfile in $(find . -name "*.ces");  do

rm $fullfile

done
for fullfile in $(find . -name "*.cfg");  do

rm $fullfile

done
for fullfile in $(find . -name "*.o");  do

rm $fullfile

done

