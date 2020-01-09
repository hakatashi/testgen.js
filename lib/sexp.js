const assert = require('assert');

// Simple encoder that produces stringified s-expressions that are compatible with CVC4
const encodeElement = (sexp) => {
  if (Array.isArray(sexp)) {
    return `(${sexp.map((element) => encodeElement(element)).join(' ')})`;
  }
  if (typeof sexp === 'number') {
    return sexp.toString();
  }
  if (typeof sexp === 'string') {
    return sexp;
  }
  return sexp;
};

const encode = (expressions) => {
  assert(Array.isArray(expressions));
  return expressions.map((expression) => encodeElement(expression)).join('\n');
};

module.exports.encode = encode;