module.exports.parseBytecode = (input) => {
	const lines = input.split(/\r?\n/);

	const codes = [];
	for (const line of lines) {
		// comment
		if (line.trim().length === 0 || line.startsWith(';')) {
			continue;
		}

		const match = line.match(/^(?<loc>\d+):\s+(?<lineno>\d+)\s+(?<operand>.+)$/);
		if (match === null) {
			throw new Error(`Parse error: "${line}"`);
		}

		const {loc, lineno, operand} = match.groups;
		const [mnemonic, ...args] = operand.replace(/\(.+?\)/g, '').trim().split(/\s+/);

		codes.push({
			loc: parseInt(loc),
			lineno: parseInt(lineno),
			mnemonic,
			args,
		});
	}

	console.log(codes);
};