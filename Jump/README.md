### [题目信息]：

出题人: Lurkrul

考点: BM算法, 模逆元, SMT/SAT

题目描述:

```
Symmetric algorithms are divided into two main categories: stream cipher and block cipher. Can you tell me the differences between them?
```

### [题目writeup]：

明文 ascii 字串足够长(大于 $2mN$ bits), 故每个字节第一个比特位均为 0

因此可以得到得到间隔为 8 的 keystream, 参考 [[1]](https://crypto.stackexchange.com/questions/59856/find-a-lfsr-given-2n-or-more-non-consecutive-keystream-bits)]

记 msgstream, keystream, cipherstream 为 $m,k,c$, 现有 $N=128,M=8$

1. 令序列 $c_j=k_{jM}, 0 \leq j < 2N$.
2. 利用 BM 算法求出 $c$ 对应的多项式 $Pol$
3. 易知 $per=2^N-1 $ 为 $c$ 的一个周期
4. $k_j=c_{(jm^{-1} \mod p)}$ , exp 中利用矩阵计算序列 $k$ 前 $2N$ 个元素
5. 求解出 $key, fill$, 得到完整的 $k$, 解出明文



另外, 也可以强行 z3, [exp_sat.py](./exp_sat.py) 里拿 z3 写了一下, 发现跑得有点慢

这里 LFSR 很简单, 可以直接化成 cnf 的形式, 然后丢给 cryptominisat

或者, 更一般的, [exp_sat_1.py](./exp_sat_1.py) z3 化简转换成 cnf, 再丢给 sat 

