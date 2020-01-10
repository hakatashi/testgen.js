const {encode} = require('./sexp.js');

module.exports.generateModels = () => {
	const sexp = [
		['set-logic', 'ALL'],
		['set-option', ':produce-models', 'true'],
		['define-sort', 'FP', [], ['_', 'FloatingPoint', 11, 53]],
		[
			'define-fun',
			'toFP',
			[['n', 'Real']],
			'FP',
			[['_', 'to_fp', 11, 53], 'RNE', 'n']
		],
		['define-fun', 'one', [], 'FP', ['toFP', 1]],
		[
			'define-fun',
			'maxSafeInteger',
			[],
			'FP',
			['toFP', 9007199254740991]
		],
		['declare-const', 'x', 'FP'],
		['assert', ['fp.isPositive', 'x']],
		['assert', ['fp.leq', 'x', 'maxSafeInteger']],
		['assert', ['fp.eq', ['fp.roundToIntegral', 'RNE', 'x'], 'x']],
		[
			'assert',
			[
				'not',
				[
					'fp.eq',
					['fp.sub', 'RNE', ['fp.add', 'RNE', 'one', 'x'], 'x'],
					'one'
				]
			]
		],
		['check-sat'],
		['get-model']
	];

	return encode(sexp);
}