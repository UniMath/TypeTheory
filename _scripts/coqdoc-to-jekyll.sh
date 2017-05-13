
# Usage:
# run “coqdoc-to-jekyll.sh your-tag” to process all the html files in “coqdoc/your-tag” appropriately

for filename in coqdoc/$1/*.html; do
# delete first 10 lines
  sed -i .bak '1,10d' $filename
# delete last 3 lines:
  sed -i .bak -e :a -e '$d;N;2,3ba' -e 'P;D' $filename
# prepend header and append footer, via temporary file
  cat _includes/coqdoc-start.html >> $filename.temp
  perl -pi -e "s/THETITLE/$(basename "$filename" .html)/g" $filename.temp
  cat $filename >> $filename.temp
  cat _includes/coqdoc-end.html >> $filename.temp
# move back
  mv $filename.temp $filename
done
rm coqdoc/$1/*.html.bak
  
