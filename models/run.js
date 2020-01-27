const {inspect} = require('util');
const fs = require('fs-extra');
const {constructGraph, listPaths, analyzePath} = require('../lib/analyzer.js');
const {decode} = require('../lib/sexp.js');
const {solve} = require('../lib/solver.js');
const {compileFunction, fp2num} = require('../lib/utils.js');
const solver1 = require('./abc148_a/solver1.js');

(async () => {
	console.log('\n\n===== CODE =====');
	console.log(solver1.toString());

	const codes = await compileFunction(solver1);
	const codeBlocks = constructGraph(codes);

	console.log('\n\n===== GRAPH ANALYSIS =====');
	console.log(inspect(codeBlocks, {depth: null}));

	const paths = listPaths(codeBlocks);
	console.log('\n\n===== VALID EXECUTION PATHS =====');
	console.log(paths);

	const spec = await fs.readFile(`${__dirname}/abc148_a/spec.smt2`);

	const corners = [];

	console.log('\n\n===== EXECUTION PATHS ANALYSIS =====');
	for (const path of paths) {
		console.log('Solving for path', path, '...');

		// place-in answer
		const {conditions, ret} = (() => {
			if (paths.length === 1) {
				const num = parseInt(solver1.toString().match(/\d/)[0]);

				return {
					conditions: [],
					ret: ['fp.sub', 'RNE', ['toFP', num], ['fp.add', 'RNE', 'x', 'y']],
				};
			}
			const result = analyzePath(path, codeBlocks);
			return {
				conditions: result.conditions,
				ret: ['toFP', result.ret],
			};
		})();
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
				node[1] = ret;
			}
		};

		dfs(specExp);

		const output = await solve(specExp);
		const result = output.split('\n')[0];
		console.log(result);

		if (result === 'sat') {
			const matches = Array.from(output.matchAll(/\(fp (.+?)\)/g));
			corners.push({x: fp2num(matches[0][1]), y: fp2num(matches[1][1])});
		}
	}

	console.log('\n\n===== RESULT ===');


	if (corners.length === 0) {
		console.log('No corner cases found :)');
	} else {
		console.log('Corner cases found!!!!! :(');
		console.log(corners);
	}
})();
