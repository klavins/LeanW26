mkdir -p dist
mkdir -p  dist/node_modules
cp  *.html *.js *.css *.json dist
cp -r src dist

mkdir -p  dist/node_modules/github-markdown-css
cp -v node_modules/github-markdown-css/github-markdown.css dist/node_modules/github-markdown-css

mkdir -p  dist/node_modules/js-cookie/
mkdir -p  dist/node_modules/js-cookie/src/
cp node_modules/js-cookie/src/js.cookie.js dist/node_modules/js-cookie/src

mkdir -p  dist/node_modules/showdown
mkdir -p  dist/node_modules/showdown/dist
cp node_modules/showdown/dist/showdown.min.js dist/node_modules/showdown/dist

mkdir -p  dist/node_modules/showdown-katex
mkdir -p  dist/node_modules/showdown-katex/dist
cp node_modules/showdown-katex/dist/showdown-katex.min.js dist/node_modules/showdown-katex/dist

mkdir -p  dist/node_modules/react
mkdir -p  dist/node_modules/react/umd
cp  node_modules/react/umd/react.production.min.js dist/node_modules/react/umd

mkdir -p  dist/node_modules/react-dom
mkdir -p  dist/node_modules/react-dom/umd
cp node_modules/react-dom/umd/react-dom.production.min.js dist/node_modules/react-dom/umd

