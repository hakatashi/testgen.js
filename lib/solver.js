const {spawn} = require('child_process');
const concatStream = require('concat-stream');
const fs = require('fs-extra');
const tmp = require('tmp');
const {encode} = require('./sexp.js');

module.exports.solve = async (sexp) => {
	const sexpString = encode(sexp);
	console.log(sexpString);

	const {path, cleanup} = await new Promise((resolve, reject) => {
		// eslint-disable-next-line no-shadow
		tmp.file((error, path, fd, cleanup) => {
			if (error) {
				reject(error);
			} else {
				resolve({path, cleanup});
			}
		});
	});

	let resultBuffer = null;
	try {
		await fs.writeFile(path, sexpString);

		const execution = spawn('cvc4', ['--lang', 'smt2', path]);

		resultBuffer = await new Promise((resolve) => {
			const cat = concatStream({encoding: 'buffer'}, (result) => resolve(result));
			execution.stdout.pipe(cat);
		});
	} finally {
		cleanup();
	}

	return resultBuffer.toString();
};
