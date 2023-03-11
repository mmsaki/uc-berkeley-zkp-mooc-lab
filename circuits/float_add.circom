pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    signal input in;
    signal output out;

    signal bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <== 1;
    }

    component bits2Num = Bits2Num(b);
    bits2Num.bits <== bits;
    signal sum_of_bits <== bits2Num.out;

    for (var i = 0; i < b; i++) {
        bits[i] * (1 - bits[i]) === 0;
    }

    component less_than = LessThan(252);
    less_than.in[0] <== in;
    less_than.in[1] <== sum_of_bits;
    out <== less_than.out;
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(shift) {
    signal input x;
    signal output y;

    // TODO
    var right = shift - 1;
    if (right < 0) {
        right = 0;
    }

    signal results[shift];
    for (var i = 0; i < shift; i ++) {
        results[i] <-- x >> (i + 1);
    }

    for (var i = 1; i < shift; i ++) {
        (results[i - 1] - results[i] * 2) * (results[i - 1] - results[i] * 2 - 1) === 0;
    }

    y <== results[right];
}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    component right_shift = RightShift(round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;

    // TODO
    assert(shift < shift_bound || skip_checks);

    signal exp[shift_bound];
    for (var i = 0; i < shift_bound; i ++) {
        exp[i] <== 2**(2**i); // 2**i corresponds to the value of the shift bits, 2**bit_value is x**b_i
    }

    var NUM_BITS = 25;

    signal tmp[NUM_BITS];
    signal results[NUM_BITS];

    results[0] <== x;
    component num2Bits = Num2Bits(NUM_BITS);
    num2Bits.in <== shift;
    signal shift_bits[NUM_BITS] <== num2Bits.bits;
    for (var i = 0; i < NUM_BITS; i ++) {
        tmp[i] <== shift_bits[i] * exp[i] + (1 - shift_bits[i]);
        if (i < NUM_BITS - 1) {
            results[i + 1] <== results[i] * tmp[i];
        } else {
            y <== results[i] * tmp[i];
        }
    }
}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];

    // TODO
    assert((skip_checks == 0 && in != 0) || skip_checks == 1);

    component n2b = Num2Bits(b + 1);
    n2b.in <== in;
    var one_bits[b];
    for (var i = 0; i < b; i ++) {
        one_bits[i] = n2b.bits[i];
    }

    // convert all low bits to 1, e.g., [1, 1, ..., 1, 0, 0]
    for (var i = b - 2; i >= 0; i --) {
        one_bits[i] = (1 - one_bits[i]) * one_bits[i + 1] + one_bits[i];
    }

    // convert one_bits into [0, 0, ..., 1, 0, 0], i.e., one_hot
    one_hot[b - 1] <== one_bits[b - 1];
    for (var i = b - 2; i >= 0; i --) {
        one_hot[i] <-- (1 - one_bits[i + 1]) * one_bits[i];
        (1 - one_hot[i]) * one_hot[i] === 0;
    }
}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // TODO
    assert((e == 0 && m == 0) || (skip_checks == 0 && m != 0) || skip_checks);

    component msnzb = MSNZB(P + 1);
    msnzb.in <== m;
    msnzb.skip_checks <== skip_checks;
    signal one_hot[P + 1] <== msnzb.one_hot;
    var ell = 0;
    for (var i = 0; i < P + 1; i ++) {
        ell += i * one_hot[i];
    }
    e_out <== e + ell - p;

    signal shift <== P - ell;
    component left_shift = LeftShift(252);
    left_shift.x <== m;
    left_shift.shift <== shift;
    left_shift.skip_checks <== skip_checks;
    m_out <== left_shift.y;

    assert(skip_checks || (m_out >= 2**P && m_out < 2**(P+1)));
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    // TODO
    assert(e[0] != 0 || m[0] == 0);
    assert(e[1] != 0 || m[1] == 0);

    var P = 2*p + 1;

    assert(m[0] == 0 || m[0] >= 2**p);
    assert(m[1] == 0 || m[1] >= 2**p);

    var shift_bound = 252;
    var less_check_bound = 252;
    var skip_checks = 0;

    component check_left = CheckWellFormedness(k, p);
    check_left.e <== e[0];
    check_left.m <== m[0];
    component check_right = CheckWellFormedness(k, p);
    check_right.e <== e[1];
    check_right.m <== m[1];

    component left_shift_1 = LeftShift(shift_bound);
    left_shift_1.x <== e[0];
    left_shift_1.shift <== p + 1;
    left_shift_1.skip_checks <== skip_checks;
    signal mgn_0 <== left_shift_1.y + m[0];

    component left_shift_2 = LeftShift(shift_bound);
    left_shift_2.x <== e[1];
    left_shift_2.shift <== p + 1;
    left_shift_2.skip_checks <== skip_checks;
    signal mgn_1 <== left_shift_2.y + m[1];

    signal alpha_e;
    signal alpha_m;
    signal beta_e;
    signal beta_m;

    component less_than = LessThan(less_check_bound);
    less_than.in[0] <== mgn_0;
    less_than.in[1] <== mgn_1;
    signal is_less <== less_than.out;

    component switcher_e = Switcher();
    switcher_e.sel <== is_less;
    switcher_e.L <== e[0];
    switcher_e.R <== e[1];
    alpha_e <== switcher_e.outL;
    beta_e <== switcher_e.outR;

    component switcher_m = Switcher();
    switcher_m.sel <== is_less;
    switcher_m.L <== m[0];
    switcher_m.R <== m[1];
    alpha_m <== switcher_m.outL;
    beta_m <== switcher_m.outR;

    signal diff <== alpha_e - beta_e;
    component is_diff_greater = LessThan(less_check_bound);
    is_diff_greater.in[0] <== p + 1;
    is_diff_greater.in[1] <== diff;

    component is_alpha_e_zero = IsZero();
    is_alpha_e_zero.in <== alpha_e;

    signal should_skip <== is_diff_greater.out + is_alpha_e_zero.out;

    component left_shift = LeftShift(shift_bound);
    left_shift.x <== alpha_m * (1 - should_skip);
    left_shift.shift <== diff;
    left_shift.skip_checks <== should_skip;
    
    component normalize = Normalize(k, p, P);
    normalize.e <== beta_e;
    normalize.m <== (left_shift.y + beta_m);
    normalize.skip_checks <== should_skip;

    component round_and_check = RoundAndCheck(k, p, P);
    round_and_check.e <== normalize.e_out * (1 - should_skip);
    round_and_check.m <== normalize.m_out * (1 - should_skip);

    component if_else_e = IfThenElse();
    if_else_e.cond <== should_skip;
    if_else_e.L <== alpha_e;
    if_else_e.R <== round_and_check.e_out;

    component if_else_m = IfThenElse();
    if_else_m.cond <== should_skip;
    if_else_m.L <== alpha_m;
    if_else_m.R <== round_and_check.m_out;

    e_out <== if_else_e.out;
    m_out <== if_else_m.out;
}
