mkdir -p dist
mkdir -p  dist/vendor
cp  *.html *.js *.css *.json dist
cp -r src dist

mkdir -p  dist/vendor/github-markdown-css
cp node_modules/github-markdown-css/github-markdown.css dist/vendor/github-markdown-css

mkdir -p  dist/vendor/js-cookie/
mkdir -p  dist/vendor/js-cookie/src/
cp node_modules/js-cookie/src/js.cookie.js dist/vendor/js-cookie/src

mkdir -p  dist/vendor/showdown
mkdir -p  dist/vendor/showdown/dist
cp node_modules/showdown/dist/showdown.min.js dist/vendor/showdown/dist

mkdir -p  dist/vendor/showdown-katex
mkdir -p  dist/vendor/showdown-katex/dist
cp node_modules/showdown-katex/dist/showdown-katex.min.js dist/vendor/showdown-katex/dist

mkdir -p  dist/vendor/react
mkdir -p  dist/vendor/react/umd
cp  node_modules/react/umd/react.production.min.js dist/vendor/react/umd

mkdir -p  dist/vendor/react-dom
mkdir -p  dist/vendor/react-dom/umd
cp node_modules/react-dom/umd/react-dom.production.min.js dist/vendor/react-dom/umd

cp -r img dist
