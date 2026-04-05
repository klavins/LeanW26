'use strict';

/**
 * Subverso Highlighting Module
 *
 * Renders Lean code with semantic highlighting based on subverso JSON output.
 * Walks the entire file's code structure to build a list of tokens with
 * precise character positions, then uses those to highlight code blocks.
 */

class SubversoHighlighter {
  constructor() {
    this.cache = new Map(); // Cache loaded JSON by module path
    this.tokenCache = new Map(); // Cache computed token positions
  }

  /**
   * Convert a deck path like "src/Logic/Propositional.md" to subverso JSON path
   */
  deckPathToSubversoPath(deckPath) {
    return deckPath
      .replace(/^src\//, 'subverso/')
      .replace(/\.md$/, '.json');
  }

  /**
   * Load subverso JSON for a given deck path
   */
  async loadModule(deckPath) {
    const jsonPath = this.deckPathToSubversoPath(deckPath);

    if (this.cache.has(jsonPath)) {
      return this.cache.get(jsonPath);
    }

    try {
      const response = await fetch(jsonPath);
      if (!response.ok) {
        console.warn(`Failed to load subverso data: ${jsonPath}`);
        return null;
      }
      const data = await response.json();
      this.cache.set(jsonPath, data);
      return data;
    } catch (e) {
      console.warn(`Error loading subverso data: ${e}`);
      return null;
    }
  }

  /**
   * Get CSS class for a token kind
   */
  tokenKindToClass(kind) {
    if (typeof kind === 'string') {
      return `sv-${kind}`;
    }
    if (kind.keyword) return 'sv-keyword';
    if (kind.const) return 'sv-const';
    if (kind.var) return 'sv-var';
    if (kind.sort) return 'sv-sort';
    if (kind.moduleName) return 'sv-module';
    return 'sv-unknown';
  }

  /**
   * Get hover info for a token
   */
  getTokenHoverInfo(kind) {
    if (typeof kind === 'string') return null;

    if (kind.const) {
      return {
        signature: kind.const.signature,
        docs: kind.const.docs,
        name: kind.const.name?.join('.')
      };
    }
    if (kind.var) {
      return { type: kind.var.type };
    }
    if (kind.keyword && kind.keyword.docs) {
      return { docs: kind.keyword.docs };
    }
    return null;
  }

  /**
   * Render a messageContents node to plain text
   */
  renderMessage(msgRef, data) {
    const node = data.messageContents?.[String(msgRef)];
    if (!node) return '';

    if (node.text !== undefined) {
      return node.text;
    }

    if (node.append) {
      return node.append.map(ref => this.renderMessage(ref, data)).join('');
    }

    if (node.term !== undefined) {
      return this.renderCodeToText(node.term, data);
    }

    return '';
  }

  /**
   * Render a code node to plain text (for messages)
   */
  renderCodeToText(codeRef, data) {
    const node = data.code[String(codeRef)];
    if (!node) return '';

    if (node.text) {
      return node.text.str;
    }

    if (node.token) {
      const tokenData = data.tokens[String(node.token.tok)];
      return tokenData?.content || '';
    }

    if (node.span) {
      return this.renderCodeToText(node.span.content, data);
    }

    if (node.seq) {
      return node.seq.highlights.map(ref => this.renderCodeToText(ref, data)).join('');
    }

    return '';
  }

  /**
   * Walk a code node, collecting tokens in order.
   * Returns { tokens: [{content, token, message?}] }
   */
  walkCodeNode(codeRef, data, result = { tokens: [] }) {
    const node = data.code[String(codeRef)];
    if (!node) return result;

    if (node.token) {
      const tokenData = data.tokens[String(node.token.tok)];
      if (tokenData) {
        result.tokens.push({ content: tokenData.content, token: tokenData });
      }
    }

    if (node.span) {
      let message = null;
      if (node.span.info) {
        for (const infoItem of node.span.info) {
          if (Array.isArray(infoItem) && infoItem[0] === 'info') {
            message = this.renderMessage(infoItem[1], data);
            break;
          }
        }
      }

      const beforeCount = result.tokens.length;
      this.walkCodeNode(node.span.content, data, result);

      if (message && result.tokens.length > beforeCount) {
        // Attach message to the first token in this span
        result.tokens[beforeCount].message = message;
      }
    }

    if (node.seq) {
      for (const ref of node.seq.highlights) {
        this.walkCodeNode(ref, data, result);
      }
    }

    return result;
  }

  /**
   * Build per-item token lists from module data.
   * Returns { items: [{startLine, endLine, tokens}] }
   */
  buildFileTokens(moduleData) {
    const items = [];

    for (const item of moduleData.items) {
      const range = item.range;
      if (!range) continue;

      const result = this.walkCodeNode(item.code, moduleData.data);
      if (result.tokens.length === 0) continue;

      items.push({
        startLine: range.start.line,
        endLine: range.end.line,
        tokens: result.tokens
      });
    }

    return { items };
  }

  /**
   * Highlight a code block by sequentially matching tokens against the
   * actual code block text. This avoids offset issues caused by subverso's
   * code tree omitting some source content (e.g. tactic internals).
   */
  highlightCodeBlock(codeElement, fileTokens) {
    const wrapper = codeElement.closest('.lean-code');
    if (!wrapper) return false;

    const blockStartLine = parseInt(wrapper.dataset.startLine);
    const blockEndLine = parseInt(wrapper.dataset.endLine);

    if (isNaN(blockStartLine) || isNaN(blockEndLine)) return false;

    const originalText = codeElement.textContent;

    // Collect tokens from all items that overlap this code block
    let orderedTokens = [];
    for (const item of fileTokens.items) {
      if (item.endLine < blockStartLine || item.startLine > blockEndLine) continue;
      for (const t of item.tokens) {
        orderedTokens.push(t);
      }
    }

    if (orderedTokens.length === 0) {
      codeElement.innerHTML = this.escapeHtml(originalText);
      codeElement.classList.add('sv-highlighted');
      return true;
    }

    // Sequentially find each token's content in the code block text.
    // Tokens come in source order from the tree walk, so we search
    // forward from the last match position.
    let matchedTokens = [];
    let searchFrom = 0;

    for (const t of orderedTokens) {
      const content = t.content;
      const isWord = /^\w/.test(content);
      let pos = searchFrom;

      while (pos < originalText.length) {
        const idx = originalText.indexOf(content, pos);
        if (idx === -1) break;

        // For word-like tokens, ensure we're not matching inside a larger
        // identifier (e.g. "intro" inside "And.intro")
        if (isWord) {
          const before = idx > 0 ? originalText[idx - 1] : ' ';
          const after = idx + content.length < originalText.length
            ? originalText[idx + content.length] : ' ';
          if (/[\w.]/.test(before) || /\w/.test(after)) {
            pos = idx + 1;
            continue;
          }
        }

        matchedTokens.push({
          start: idx,
          end: idx + content.length,
          token: t.token,
          message: t.message
        });
        searchFrom = idx + content.length;
        break;
      }
    }

    if (matchedTokens.length === 0) {
      codeElement.innerHTML = this.escapeHtml(originalText);
      codeElement.classList.add('sv-highlighted');
      return true;
    }

    // Build highlighted HTML
    let html = '';
    let lastEnd = 0;

    for (const t of matchedTokens) {
      if (t.start < lastEnd) continue;

      if (t.start > lastEnd) {
        html += this.escapeHtml(originalText.slice(lastEnd, t.start));
      }

      let cssClass = 'sv-info';
      if (t.token) {
        cssClass = this.tokenKindToClass(t.token.kind);
      }

      let title = '';
      if (t.message) {
        title = t.message;
      } else if (t.token) {
        const hoverInfo = this.getTokenHoverInfo(t.token.kind);
        if (hoverInfo) {
          title = this.formatHoverTitle(hoverInfo);
        }
      }

      let attrs = `class="${cssClass}${title ? ' sv-has-tooltip' : ''}"`;
      if (title) {
        attrs += ` data-tooltip="${this.escapeAttr(title)}"`;
      }

      html += `<span ${attrs}>${this.escapeHtml(originalText.slice(t.start, t.end))}</span>`;
      lastEnd = t.end;
    }

    if (lastEnd < originalText.length) {
      html += this.escapeHtml(originalText.slice(lastEnd));
    }

    codeElement.innerHTML = html;
    codeElement.classList.add('sv-highlighted');
    return true;
  }

  /**
   * Highlight all code blocks on the page for a given deck
   */
  async highlightAll(deckPath) {
    console.log('subverso highlightAll called with:', deckPath);

    const moduleData = await this.loadModule(deckPath);
    if (!moduleData) {
      console.warn('No module data loaded');
      return;
    }
    console.log('Module data loaded, items:', moduleData.items);

    // Build file tokens (cached per module)
    const cacheKey = deckPath;
    let fileTokens;
    if (this.tokenCache.has(cacheKey)) {
      fileTokens = this.tokenCache.get(cacheKey);
    } else {
      fileTokens = this.buildFileTokens(moduleData);
      this.tokenCache.set(cacheKey, fileTokens);
      console.log('Built file tokens, items:', fileTokens.items.length);
    }

    const codeBlocks = document.querySelectorAll('.lean-code code');
    console.log('Found code blocks:', codeBlocks.length);

    for (const block of codeBlocks) {
      if (!block.classList.contains('sv-highlighted')) {
        const wrapper = block.closest('.lean-code');
        console.log('Highlighting block, wrapper:', wrapper, 'lines:', wrapper?.dataset.startLine, '-', wrapper?.dataset.endLine);
        this.highlightCodeBlock(block, fileTokens);
      }
    }
  }

  formatHoverTitle(info) {
    let parts = [];
    if (info.signature) {
      parts.push(info.signature);
    }
    if (info.type) {
      parts.push(`: ${info.type}`);
    }
    if (info.docs) {
      // Truncate long docs for title attribute
      const docs = info.docs.length > 200 ? info.docs.slice(0, 200) + '...' : info.docs;
      parts.push(docs);
    }
    return parts.join('\n');
  }

  escapeHtml(str) {
    return str
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;');
  }

  escapeAttr(str) {
    return str
      .replace(/&/g, '&amp;')
      .replace(/"/g, '&quot;');
  }
}

// Global instance
window.subversoHighlighter = new SubversoHighlighter();
