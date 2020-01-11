module.exports = (x, y) => {
	if (x === 1) {
		if (y === 2) {
			return 3;
		} else if (y === 3) {
			return 2;
		}
	} else if (x === 2) {
		if (y === 1) {
			return 3;
		} else if (y === 3) {
			return 1;
		}
	} else if (x === 3) {
		if (y === 1) {
			return 2;
		} else if (y === 2) {
			return 1;
		}
	}
};
