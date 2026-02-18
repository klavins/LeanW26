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
   * Walk a code node, collecting text and tokens with positions.
   * Returns { text: string, tokens: [{start, end, token, message?}] }
   */
  walkCodeNode(codeRef, data, result = { text: '', tokens: [] }) {
    const node = data.code[String(codeRef)];
    if (!node) return result;

    if (node.text) {
      result.text += node.text.str;
    }

    if (node.token) {
      const tokenData = data.tokens[String(node.token.tok)];
      if (tokenData) {
        const start = result.text.length;
        result.text += tokenData.content;
        const end = result.text.length;
        result.tokens.push({ start, end, token: tokenData });
      }
    }

    if (node.span) {
      // Check for info (messages like #check output)
      let message = null;
      if (node.span.info) {
        for (const infoItem of node.span.info) {
          if (Array.isArray(infoItem) && infoItem[0] === 'info') {
            message = this.renderMessage(infoItem[1], data);
            console.log('Found span info:', infoItem, 'message:', message);
            break;
          }
        }
      }

      // Record the span's position
      const start = result.text.length;
      this.walkCodeNode(node.span.content, data, result);
      const end = result.text.length;

      // If there's a message, attach it to a synthetic token for this span
      if (message) {
        console.log('Adding message token:', { start, end, message });
        result.tokens.push({ start, end, message });
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
   * Build complete file content and token positions from all commands
   */
  buildFileTokens(moduleData) {
    const jsonPath = this.deckPathToSubversoPath(''); // Just for cache key

    let fullText = '';
    let allTokens = [];

    for (const item of moduleData.items) {
      const result = this.walkCodeNode(item.code, moduleData.data);

      // Adjust token positions to be relative to full file
      for (const t of result.tokens) {
        allTokens.push({
          start: fullText.length + t.start,
          end: fullText.length + t.end,
          token: t.token,
          message: t.message
        });
      }

      fullText += result.text;
    }

    return { text: fullText, tokens: allTokens };
  }

  /**
   * Convert character offset to line/column (1-based)
   */
  offsetToLineCol(text, offset) {
    let line = 1;
    let col = 1;
    for (let i = 0; i < offset && i < text.length; i++) {
      if (text[i] === '\n') {
        line++;
        col = 1;
      } else {
        col++;
      }
    }
    return { line, col };
  }

  /**
   * Convert line/column (1-based) to character offset
   */
  lineColToOffset(text, line, col) {
    let currentLine = 1;
    let offset = 0;

    while (offset < text.length && currentLine < line) {
      if (text[offset] === '\n') {
        currentLine++;
      }
      offset++;
    }

    // Now at the start of the target line, add column offset
    return offset + col - 1;
  }

  /**
   * Get tokens within a line range
   */
  getTokensInRange(fileTokens, startLine, endLine) {
    const { text, tokens } = fileTokens;

    const startOffset = this.lineColToOffset(text, startLine, 1);
    // End of endLine = start of endLine+1, minus 1 char (or end of file)
    let endOffset = this.lineColToOffset(text, endLine + 1, 1);
    if (endOffset > startOffset) endOffset--; // Don't include the newline of the next line

    return tokens.filter(t => t.start >= startOffset && t.end <= endOffset + 1);
  }

  /**
   * Highlight a code block using precise token positions
   */
  highlightCodeBlock(codeElement, fileTokens) {
    const wrapper = codeElement.closest('.lean-code');
    if (!wrapper) return false;

    const startLine = parseInt(wrapper.dataset.startLine);
    const endLine = parseInt(wrapper.dataset.endLine);

    if (isNaN(startLine) || isNaN(endLine)) return false;

    const originalText = codeElement.textContent;
    const { text: fullText } = fileTokens;

    // Get start offset in full file for our code block
    const blockStartOffset = this.lineColToOffset(fullText, startLine, 1);

    // Get tokens in range
    const tokensInRange = this.getTokensInRange(fileTokens, startLine, endLine);
    const messageTokens = tokensInRange.filter(t => t.message);
    console.log('Tokens in range for lines', startLine, '-', endLine, ':', tokensInRange.length, 'total,', messageTokens.length, 'with messages');
    if (messageTokens.length > 0) {
      console.log('Message tokens:', messageTokens);
    }

    if (tokensInRange.length === 0) {
      // No tokens - just escape and return
      codeElement.innerHTML = this.escapeHtml(originalText);
      codeElement.classList.add('sv-highlighted');
      return true;
    }

    // Build highlighted HTML
    // Adjust token positions to be relative to code block start
    const adjustedTokens = tokensInRange.map(t => ({
      start: t.start - blockStartOffset,
      end: t.end - blockStartOffset,
      token: t.token,
      message: t.message
    })).filter(t => t.start >= 0 && t.end <= originalText.length);

    // Sort by start position, then prefer tokens with messages
    adjustedTokens.sort((a, b) => {
      if (a.start !== b.start) return a.start - b.start;
      // If same start, prefer message tokens
      if (a.message && !b.message) return -1;
      if (b.message && !a.message) return 1;
      return 0;
    });

    let html = '';
    let lastEnd = 0;

    for (const t of adjustedTokens) {
      // Skip overlapping tokens (already rendered)
      if (t.start < lastEnd) continue;

      // Add unhighlighted text before this token
      if (t.start > lastEnd) {
        html += this.escapeHtml(originalText.slice(lastEnd, t.start));
      }

      // Determine CSS class
      let cssClass = 'sv-info';
      if (t.token) {
        cssClass = this.tokenKindToClass(t.token.kind);
      }

      // Determine title (prefer message over hover info)
      let title = '';
      if (t.message) {
        title = t.message;
      } else if (t.token) {
        const hoverInfo = this.getTokenHoverInfo(t.token.kind);
        if (hoverInfo) {
          title = this.formatHoverTitle(hoverInfo);
        }
      }

      let attrs = `class="${cssClass}"`;
      if (title) {
        attrs += ` title="${this.escapeAttr(title)}"`;
      }

      html += `<span ${attrs}>${this.escapeHtml(originalText.slice(t.start, t.end))}</span>`;
      lastEnd = t.end;
    }

    // Add remaining text
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
      console.log('Built file tokens, total text length:', fileTokens.text.length, 'tokens:', fileTokens.tokens.length);
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
