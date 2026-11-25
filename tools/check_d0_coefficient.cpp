// paper.tex (colliding poles) Section 9.  Search for two-vector levels where the d^{k+1} coefficient at d = 0 of the
// top-layer polynomial P_N(d) (eq. (8.1)) vanishes.
//
// By Prop 9.1, N^pm_k/gamma^pm_k = c_k (pm rho)^k d^k + O(d^{k+1}); by Lemma 6.5,
// H_M(c_star, mu, d) = d * dH_M + O(d^2) with
//   dH_M = (2pp'/(p-p')) * f(M, m),  f(M, m) = sum_{r's'=M} x/(m^2-x^2),  x = p'r'-ps',
// where mu = (m^2-(p'-p)^2)/(4pp').  Hence
//   [d^{k+1}] P_N = c_k rho^k (2pp'/(p-p')) * ( f(M+, m+) + (-1)^k f(M-, m-) ).
// The program prints every (p,p',r,s,k,N) with max(l+,l-) < N < l_{k+1} where
// G := f(M+, m+) + (-1)^k f(M-, m-) is zero, and a heartbeat per (p,p').
//
// Build: clang++ -O3 -march=native -o check_d0_coefficient tools/check_d0_coefficient.cpp -lgmpxx -lgmp
// Usage: ./check_d0_coefficient 13 3   (paper, Section 9: 528180 levels, 0 zeros, about 5 s)
#include <gmpxx.h>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <numeric>
#include <algorithm>

typedef long long ll;

static void momenta(ll p, ll pp, ll r, ll s, int k, ll &mp, ll &mm) {
    ll n0 = std::llabs(pp * r - p * s), n1 = pp * r + p * s, N0 = 2 * p * pp;
    if (k % 2) { ll j = (k - 1) / 2; mp = n1 + j * N0; mm = (j + 1) * N0 - n1; }
    else { ll j = k / 2; mp = j * N0 + n0; mm = j * N0 - n0; }
}

int main(int argc, char **argv) {
    ll PMAX = argc > 1 ? atoll(argv[1]) : 12;
    int KMAX = argc > 2 ? atoi(argv[2]) : 3;
    time_t t0 = time(nullptr);
    ll cases = 0, zeros = 0, bad = 0;
    for (ll p = 2; p <= PMAX; ++p)
        for (ll pp = 2; pp <= PMAX; ++pp) {
            if (p == pp || std::gcd(p, pp) != 1) continue;
            ll pairs_cases = 0;
            for (ll r = 1; r < p; ++r)
                for (ll s = 1; s < pp; ++s) {
                    ll n0 = pp * r - p * s;
                    for (int k = 1; k <= KMAX; ++k) {
                        ll mp, mm, mp2, mm2;
                        momenta(p, pp, r, s, k, mp, mm);
                        momenta(p, pp, r, s, k + 1, mp2, mm2);
                        ll lp = (mp * mp - n0 * n0) / (4 * p * pp);
                        ll lm = (mm * mm - n0 * n0) / (4 * p * pp);
                        ll lp2 = (mp2 * mp2 - n0 * n0) / (4 * p * pp);
                        ll lm2 = (mm2 * mm2 - n0 * n0) / (4 * p * pp);
                        ll lnext = std::min(lp2, lm2);
                        for (ll N = std::max(lp, lm) + 1; N < lnext; ++N) {
                            ll Mp = N - lp, Mm = N - lm;
                            mpq_class G = 0;
                            bool sing = false;
                            for (int sg = 0; sg < 2; ++sg) {
                                ll M = sg ? Mm : Mp, m = sg ? mm : mp;
                                mpq_class f = 0;
                                for (ll a = 1; a <= M; ++a) {
                                    if (M % a) continue;
                                    ll b = M / a, x = pp * a - p * b;
                                    ll den = m * m - x * x;
                                    if (den == 0) { sing = true; continue; }
                                    { mpq_class q((long)x, (long)den); q.canonicalize(); f += q; }
                                }
                                if (sg && (k % 2)) G -= f; else G += f;
                            }
                            ++cases; ++pairs_cases;
                            if (sing) { ++bad; printf("SINGULAR p=%lld p'=%lld r=%lld s=%lld k=%d N=%lld\n", p, pp, r, s, k, N); }
                            else if (G == 0) {
                                ++zeros;
                                printf("ZERO p=%lld p'=%lld r=%lld s=%lld k=%d N=%lld M+=%lld M-=%lld m+=%lld m-=%lld\n",
                                       p, pp, r, s, k, N, Mp, Mm, mp, mm);
                            }
                        }
                    }
                }
            printf("[%lds] done (p,p')=(%lld,%lld): %lld levels; totals %lld levels, %lld zeros, %lld singular\n",
                   (long)(time(nullptr) - t0), p, pp, pairs_cases, cases, zeros, bad);
            fflush(stdout);
        }
    printf("FINAL levels=%lld zeros=%lld singular=%lld\n", cases, zeros, bad);
    return 0;
}
