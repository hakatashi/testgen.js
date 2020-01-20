const {inspect} = require('util');
const fs = require('fs-extra');
const {constructGraph, listPaths} = require('../lib/analyzer.js');
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
	const specExp = decode(spec.toString());

	for (const path of paths) {
		console.log('Solving for path', path, '...');

		// place-in answer
		await solve(specExp);
	}
})();
