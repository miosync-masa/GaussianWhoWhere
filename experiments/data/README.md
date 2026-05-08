# Precomputed Data

These CSVs require significant compute time to regenerate.
Included for reproducibility.

## Files

| File | Rows | Compute | Description |
|------|------|---------|-------------|
| phase2_colab_primary_10.csv | 100,000 | ~12h (H100) | Bridge C response operators, FE-broken |
| phase1a_prime_v4.csv | 40,000 | ~4h | FE-preserving Where response, 4 conditions |
| phase2_colab_stability_10.csv | — | ~1h | ε-stability check |
| bridge_c_rmt_SI_data.csv | 2,000 | ~12min | Z'(γ) + true adjacent spacings |

## Zero data source

zeros6.txt (2,001,052 zeros) from LMFDB.
Not included due to size. Obtain from:
https://www.lmfdb.org/zeros/zeta/
