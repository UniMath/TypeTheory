
# Usage:
# run “_scripts/coqdoc-to-jekyll.sh coqdoc/your-tag” to process all html files
# in “coqdoc/your-tag” appropriately, removing the standard coqdoc-produced
# header and footer blocks and replacing them with a yaml frontmatter block
# to integrate them into the ambient Jekyll theme.

for filename in $1/*.html; do
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

perl -pi -e "s/title: index/title: Index/g" $1/index.html
perl -pi -e "s/title: toc/title: Table of contents/g" $1/toc.html

rm $1/*.html.bak
  
