const {inspect} = require('util');
const {constructGraph} = require('../lib/analyzer.js');
const {compileFunction} = require('../lib/utils.js');

(async () => {
	const codes = await compileFunction((n) => {
		if (n > 0) {
			return n;
		}
		if (n < 0) {
			return -n;
		}
		return 0;
	});

	console.log(inspect(constructGraph(codes), {depth: null}));
})();
