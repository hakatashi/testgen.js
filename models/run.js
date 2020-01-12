const {inspect} = require('util');
const {constructGraph, listPaths} = require('../lib/analyzer.js');
const {compileFunction} = require('../lib/utils.js');
const solver1 = require('./abc148_a/solver1.js');

(async () => {
	console.log('===== CODE =====');
	console.log(`${solver1.toString()}\n`);

	const codes = await compileFunction(solver1);
	const codeBlocks = constructGraph(codes);

	console.log('===== GRAPH ANALYSIS =====');
	console.log(`${inspect(codeBlocks, {depth: null})}\n`);

	console.log(listPaths(codeBlocks));
})();
