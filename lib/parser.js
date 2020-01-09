const {inspect} = require('util');
const {last} = require('lodash');

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

	const codeBlocks = [];
	let currentBlock = {
		loc: 0,
		codes: [],
		children: [],
	};

	const targetMap = new Map();

	for (const code of codes) {
		if (code.mnemonic === 'JumpTarget') {
			if (currentBlock.codes.length > 0) {
				codeBlocks.push(currentBlock);
			}

			currentBlock = {
				loc: null,
				codes: [],
				children: [],
			};
		}

		if (currentBlock.codes.length === 0 && codeBlocks.length > 0) {
			currentBlock.loc = code.loc;
			if (last(last(codeBlocks).codes).mnemonic !== 'Return') {
				codeBlocks[codeBlocks.length - 1].children.push(code.loc);
			}
		}

		currentBlock.codes.push(code);

		if (code.mnemonic === 'IfEq') {
			codeBlocks.push(currentBlock);
			
			currentBlock = {
				loc: null,
				codes: [],
				children: [],
			};
			continue;
		}
	}

	if (currentBlock.codes.length > 0) {
		codeBlocks.push(currentBlock)
	}

	console.log(inspect(codeBlocks, {depth: null}));
};