const assert = require('assert');
const elparser = require('elparser');

// Simple encoder that produces stringified s-expressions that are compatible with CVC4
const encodeElement = (sexp) => {
  if (Array.isArray(sexp)) {
    return `(${sexp.map((element) => encodeElement(element)).join(' ')})`;
  }
  if (sexp === null) {
    return '()';
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

const decode = (string) => elparser.parse(string).map((exp) => exp.toJS());

module.exports.encode = encode;
module.exports.decode = decode;

