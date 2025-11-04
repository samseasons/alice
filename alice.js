a0 = 0, a1 = 1, a16 = 16, a32 = 32, a48 = 48, a64 = 64, a128 = 128

function big (a) {
  return BigInt(a)
}

function num (a) {
  return Number(a)
}

function uint8 (a) {
  return new Uint8Array(a)
}

function uint32 (a) {
  return new Uint32Array(a)
}

function pack (a) {
  let b = 0, c = a.length, d = []
  while (b < c) {
    d.push(a[b++] ^ a[b++] << 8 ^ a[b++] << 16 ^ a[b++] << 24 >> 0)
  }
  return d
}

function unpack (a) {
  let b = 0, c = a.length, d = [], e, f = 255
  while (b < c) {
    e = a[b++]
    d.push(e & f, e >> 8 & f, e >> 16 & f, e >> 24 & f)
  }
  return d
}

function shift (a, b) {
  return a << b | a >>> a32 - b
}

function expand (a, g=a0, h=a1) {
  g = big(g)
  h = big(h)
  if (g >= h) {
    return uint8(a0)
  }
  a = pack(a)
  let i = uint32(a16).map((c, b) => a[b] | a0 + a[b + a32] | a0),
      j = uint32(a16).map((c, b) => a[b + a16] | a0 + a[b + a48] | a0)
  a = uint8(num(h - g))

  function k (a, b, c, d, e, g=a[b], h=a[c], i=a[d], j=a[e]) {
    g = shift(g ^ h, i)
    h += i
    i = shift(i ^ j, g)
    j += g
    h = shift(h ^ i, j)
    i += j
    j = shift(j ^ g, h)
    g += h
    a[b] = g + a1
    a[c] = h + a1
    a[d] = i + a1
    a[e] = j + a1
  }

  function l () {
    let a = i.slice(), b = j.slice(), c, d = a16, e = 10

    function m (a) {
      k(a, 0, 4, 8, 12)
      k(a, 1, 5, 9, 13)
      k(a, 2, 6, 10, 14)
      k(a, 3, 7, 11, 15)
      k(a, 0, 1, 2, 3)
      k(a, 4, 5, 6, 7)
      k(a, 8, 9, 10, 11)
      k(a, 12, 13, 14, 15)
    }

    while (e--) {
      m(a)
      m(b)
      if (e % 5 == a0) {
        c = d
        while (c--) {
          b[c] = a[c] += b[c]
        }
        b.reverse()
      }
    }
    return a
  }

  let m = 2n ** 32n

  function n (a) {
    let b = a0, c = a16, d = 0n
    while (b < c) {
      d = d * m + big(a[b++])
    }
    return d
  }

  function o (a, b) {
    let c = a0, d = a16
    while (c < d) {
      b[--d] = num(a % m)
      a /= m
    }
    return b
  }

  let p = 64n, q = g / p
  i = o(n(i) + q, uint32(a16))
  j = o(n(j) + q, uint32(a16))
  m = g % p
  a.set(unpack(l()).slice(num(m), num(h - g + m)))
  for (let b = g - m + p, c; b < h; b += p) {
    i[c = 15]++
    while (i[c] == a0) {
      i[--c]++
    }
    j[c = 15]++
    while (j[c] == a0) {
      j[--c]++
    }
    a.set(unpack(l()).slice(a0, num(h - b)), num(b - g))
  }
  return a
}

function reduce (a, h=a1) {
  while (a.length > a128) {
    a = [...expand(a.slice(a0, a128), a0, a64), ...a.slice(a128)]
  }
  return expand(a, a0, h)
}

function randombytes (a) {
  return crypto.getRandomValues(uint8(a))
}

seeds = 256 ** 2
sample_bytes = seeds * 32
public_bytes = sample_bytes + 256
secret_bytes = public_bytes + seeds * 4
cipher_bytes = 32
shared_bytes = 32

function crypto_kem_keypair (a, b) {
  const e = randombytes(256)
  a.set(e, secret_bytes - 256)
  b.set(e, sample_bytes)
  const p = []
  let g, h, i, j = 0, k, l, m = sample_bytes
  while (j < sample_bytes) {
    i = randombytes(4)
    h = i.reduce((a, b) => 256 * a + b)
    if (p.includes(h)) continue
    p.push(h)
    h *= 64
    g = expand(e, h, h + 64)
    l = 0
    while (l < 32) {
      k = j + l
      a[k] = g[l + 32]
      b[k] = g[l++]
    }
    j += 32
    l = 0
    while (l < 4) {
      a[m++] = i[l++]
    }
  }
}

function crypto_kem_enc (c, k, p) {
  const d = []
  for (let i = 0, l = p.length - 256; i < l;) {
    d.push(p.slice(i, i += 32).toString())
  }
  const e = p.slice(-256), f = uint8(e)
  p = []
  let g, h, i, j = 0, l, m
  while (j < cipher_bytes) {
    i = randombytes(4)
    h = i.reduce((a, b) => 256 * a + b)
    if (p.includes(h)) continue
    p.push(h)
    h *= 64
    g = expand(e, h, h + 32)
    if (d.includes(g.toString())) {
      g = expand(e, h + 32, h + 64)
      l = 0
      while (l < 32) {
        h = g[l]
        m = j + l
        c[m] = h
        f[m] += h + i[l++ % 4]
      }
      j += 32
    }
  }
  k.set(reduce(f, 32))
}

function crypto_kem_dec (c, k, p) {
  const d = []
  for (let i = 0, l = sample_bytes; i < l;) {
    d.push(p.slice(i, i += 32).toString())
  }
  const e = uint8(p.slice(-256))
  for (let h, i = 0, j, l = c.length, m; i < l;) {
    j = d.indexOf(c.slice(m = i, i += 32).toString())
    if (j == -1) return
    h = sample_bytes + j * 4
    h = p.slice(h, h + 4)
    j *= 32
    for (let i = 0; i < 32; i++) {
      e[i + m] += p[i + j] + h[i % 4]
    }
  }
  k.set(reduce(e, 32))
}

priv = uint8(secret_bytes)
pub = uint8(public_bytes)
crypto_kem_keypair(priv, pub)
ciph = uint8(cipher_bytes)
key0 = uint8(shared_bytes)
crypto_kem_enc(ciph, key0, pub)
key1 = uint8(shared_bytes)
crypto_kem_dec(ciph, key1, priv)
key0.toString() == key1.toString()