module.exports.fp2num = (input) => {
  const bytes = input.replace(/[^01]/g, '').split(/(!?.{8})/).filter((s) => s.length > 0);
  const buffer = Buffer.from(bytes.map((byte) => parseInt(byte, 2)));
  return buffer.readDoubleBE();
};