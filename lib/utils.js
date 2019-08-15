module.exports.fp2num = (input) => {
  const bytes = input.replace(/[^01]/g, '').split(/(!?.{8})/).filter((s) => s.length > 0);
  const buffer = Buffer.from(bytes.map((byte) => parseInt(byte, 2)));
  return buffer.readDoubleBE();
};

module.exports.num2fp = (input) => {
  const buffer = Buffer.alloc(8);
  buffer.writeDoubleBE(input);
  const bins = Array.from(buffer).map((byte) => byte.toString(2).padStart(8, '0')).join('');
  const chunks = [bins.slice(0, 1), bins.slice(1, 12), bins.slice(12)];
  return chunks.map((chunk) => `#b${chunk}`).join(' ');
};