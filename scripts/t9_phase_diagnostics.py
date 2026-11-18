"""Regression checks for TRS classification and both three-band phase thresholds."""
import numpy as np
from t4_aase_trsb import is_trsb, phase_rule, trsb_bounds


def main():
    for phases in ([0, 0, 0], [0, np.pi, np.pi], [0, np.pi, 0], [0.7, 0.7 + np.pi, 0.7]):
        assert not is_trsb(phases), phases
    assert is_trsb([0, np.pi / 2, np.pi / 4])
    assert is_trsb([0.7, 0.7 + np.pi / 2, 0.7 + np.pi / 4])
    lower, upper = trsb_bounds(-1.0, -2.0)
    assert np.isclose(lower, 2 / 3) and upper == 2
    for a12, expected in ((0.5, False), (1.0, True), (3.0, False)):
        phases = np.r_[0.0, phase_rule(a12, -1.0, -2.0)]
        actual = is_trsb(phases)
        assert actual == expected, (a12, phases, actual)
        print(f'a12={a12}, bounds=({lower}, {upper}), phases/pi={phases / np.pi}, TRSB={actual}')
    assert np.isinf(trsb_bounds(-1.0, -1.0)[1])
    print('PASS: real pi states preserve TRS; both strict thresholds are required.')


if __name__ == '__main__':
    main()
