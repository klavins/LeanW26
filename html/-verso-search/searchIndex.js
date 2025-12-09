const __verso_searchIndexData = {"documentStore":{"docInfo":{},"docs":{},"length":"0","save":false},"fields":["id","header","contents","context"],"index":{"contents":{"root":{"df":0,"docs":{}}},"context":{"root":{"df":0,"docs":{}}},"header":{"root":{"df":0,"docs":{}}},"id":{"root":{"df":0,"docs":{}}}},"pipeline":["trimmer","stopWordFilter","stemmer"],"ref":"id","version":"0.9.5"};

const __versoSearchIndex = elasticlunr ? elasticlunr.Index.load(__verso_searchIndexData) : null;
window.docContents = {};
window.searchIndex = elasticlunr ? __versoSearchIndex : null;
