const {last} = require('lodash');

module.exports.constructGraph = (codes) => {
	const codeBlocks = [];
	let currentBlock = {
		loc: 0,
		codes: [],
		children: [],
	};

	const codeBlockMap = new Map();

	for (const code of codes) {
		if (code.mnemonic === 'JumpTarget') {
			if (currentBlock.codes.length > 0) {
				codeBlocks.push(currentBlock);
				codeBlockMap.set(currentBlock.loc, currentBlock);
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
				last(codeBlocks).children.push(code.loc);
			}
		}

		currentBlock.codes.push(code);

		if (code.mnemonic === 'IfEq') {
			const target = parseInt(code.args[0]);
			currentBlock.children.push(target);

			codeBlocks.push(currentBlock);
			codeBlockMap.set(currentBlock.loc, currentBlock);

			currentBlock = {
				loc: null,
				codes: [],
				children: [],
			};
			continue;
		}
	}

	if (currentBlock.codes.length > 0) {
		codeBlocks.push(currentBlock);
		codeBlockMap.set(currentBlock.loc, currentBlock);
	}

	return codeBlocks;
};
