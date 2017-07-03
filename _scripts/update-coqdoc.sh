
echo "\
# (Sorry this is not actually scripted yet; scripts that go between git
# branches are very difficult to make robust.)
# 
# To update coqdoc, or add it for a new tag, run something like the
# following, with ‘master’ replaced by the branch/tag you want:

git checkout master
make html
git checkout gh-pages
mv html/* coqdoc/master/
_scripts/coqdoc-to-jekyll.sh coqdoc/master
git commit -am 'Updated coqdoc for master'
"
