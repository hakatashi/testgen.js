const {inspect} = require('util');
const fs = require('fs-extra');
const {constructGraph, listPaths, analyzePath} = require('../lib/analyzer.js');
const {decode} = require('../lib/sexp.js');
const {solve} = require('../lib/solver.js');
const {compileFunction} = require('../lib/utils.js');
const solver1 = require('./abc148_a/solver1.js');

(async () => {
	console.log('===== CODE =====');
	console.log(`${solver1.toString()}\n`);

	const codes = await compileFunction(solver1);
	const codeBlocks = constructGraph(codes);

	console.log('===== GRAPH ANALYSIS =====');
	console.log(`${inspect(codeBlocks, {depth: null})}\n`);

	const paths = listPaths(codeBlocks);
	console.log('===== VALID EXECUTION PATHS =====');
	console.log(paths);

	const spec = await fs.readFile(`${__dirname}/abc148_a/spec.smt2`);

	for (const path of paths) {
		console.log('Solving for path', path, '...');

		// place-in answer
		const {conditions, ret} = analyzePath(path, codeBlocks);
		const specExp = decode(spec.toString());

		const dfs = (node, depth = 0) => {
			for (const child of node) {
				if (Array.isArray(child)) {
					dfs(child, depth + 1);
				}
			}

			if (depth === 2 && node[0] === 'and') {
				for (const condition of conditions) {
					if (condition.not) {
						node.push(['not', [condition.operand, condition.lval, ['toFP', condition.rval]]]);
					} else {
						node.push([condition.operand, condition.lval, ['toFP', condition.rval]]);
					}
				}
			}

			if (depth === 6 && node[0] === 'ans') {
				node[1] = ['toFP', ret];
			}
		};

		dfs(specExp);

		await solve(specExp);
	}
})();
