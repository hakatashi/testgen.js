const assert = require('assert');
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

module.exports.analyzePath = (path, codeBlocksArray) => {
	const codeBlocks = new Map(codeBlocksArray.map((block) => [block.loc, block]));

	const conditions = [];
	let ret = null;

	for (const [index, loc] of path.entries()) {
		const codeBlock = codeBlocks.get(loc);
		assert(codeBlock !== undefined);

		const nextLoc = path[index + 1];

		const lastCode = last(codeBlock.codes);
		if (lastCode.mnemonic === 'IfEq') {
			const target = parseInt(lastCode.args[0]);

			let rval = null;
			let lval = null;
			let operand = null;
			for (const {mnemonic, args} of codeBlock.codes) {
				if (mnemonic === 'GetArg') {
					lval = args[0] === '0' ? 'x' : 'y';
				}
				if (mnemonic === 'One') {
					rval = 1;
				}
				if (mnemonic === 'Zero') {
					rval = 0;
				}
				if (mnemonic === 'Int8') {
					rval = parseInt(args[0]);
				}
				if (mnemonic === 'StrictEq') {
					operand = 'fp.eq';
				}
			}

			const not = nextLoc === target;

			conditions.push({rval, lval, operand, not});
		}

		if (lastCode.mnemonic === 'Return' && ret === null) {
			for (const {mnemonic, args} of codeBlock.codes) {
				if (mnemonic === 'GetArg') {
					ret = args[0] === '0' ? 'x' : 'y';
				}
				if (mnemonic === 'One') {
					ret = 1;
				}
				if (mnemonic === 'Zero') {
					ret = 0;
				}
				if (mnemonic === 'Int8') {
					ret = parseInt(args[0]);
				}
			}
		}

		if (lastCode.mnemonic === 'Goto') {
			for (const {mnemonic, args} of codeBlock.codes) {
				if (mnemonic === 'GetArg') {
					ret = args[0] === '0' ? 'x' : 'y';
				}
				if (mnemonic === 'One') {
					ret = 1;
				}
				if (mnemonic === 'Zero') {
					ret = 0;
				}
				if (mnemonic === 'Int8') {
					ret = parseInt(args[0]);
				}
			}
		}
	}

	return {conditions, ret};
};
