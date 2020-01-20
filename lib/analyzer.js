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
			const previousMnemonic = last(last(codeBlocks).codes).mnemonic;
			if (previousMnemonic !== 'Return' && previousMnemonic !== 'Goto') {
				last(codeBlocks).children.push(code.loc);
			}
		}

		currentBlock.codes.push(code);

		if (code.mnemonic === 'IfEq' || code.mnemonic === 'Goto') {
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

const dfs = (node, codeBlocks, history) => {
	const {children} = codeBlocks.get(node);
	if (children.length === 0) {
		return [history];
	}

	const paths = [];
	for (const child of children) {
		paths.push(...dfs(child, codeBlocks, [...history, child]));
	}

	return paths;
};

module.exports.listPaths = (codeBlocksArray) => {
	const codeBlocks = new Map(codeBlocksArray.map((block) => [block.loc, block]));
	const paths = dfs(0, codeBlocks, [0]);
	return paths;
};
