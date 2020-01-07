const tmp = require('tmp');
const fs = require('fs-extra');
const {spawn} = require('child_process');
const concatStream = require('concat-stream');
const {parseBytecode} = require('./parser.js');

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

module.exports.compileFunction = async (func) => {
	const source = `dissrc(${func.toString()});`;
	const {path, cleanup} = await new Promise((resolve, reject) => {
		tmp.file((error, path, fd, cleanup) => {
			if (error) {
				reject(error);
			} else {
				resolve({path, cleanup});
			}
		})
	});

	try {
		await fs.writeFile(path, source);

		const execution = spawn('js74', [path]);

		const resultBuffer = await new Promise((resolve) => {
			const cat = concatStream({encoding: 'buffer'}, (result) => resolve(result));
			execution.stdout.pipe(cat);
		});
		parseBytecode(resultBuffer.toString());
	} finally {
		cleanup();
	}
}

