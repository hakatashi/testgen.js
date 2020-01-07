const {compileFunction} = require('../lib/utils.js');

compileFunction((n) => {
	if (n > 0) {
		return n;
	}
	if (n < 0) {
		return -n;
	}
	return 0;
});
