import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.ProofSupport
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located-instruction helpers for the appended fast path

The appended Montgomery path occupies instruction indices 977..1741
(pc 1314..2862).  This module fixes the `Located` constructors, the
program-counter table and the jump-destination facts those blocks need.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

@[simp] theorem fastPC0 (i : Nat) (hi : 977 ≤ i) (hii : i ≤ 1016) :
    Artifact.submissionArtifact.instructionPC i =
      [1314,1315,1317,1318,1319,1321,1322,1323,1326,1327,1329,1330,1331,1332,1333,1336,1337,1338,1341,1342,1343,1344,1347,1348,1349,1352,1353,1354,1356,1357,1359,1360,1361,1363,1364,1365,1366,1367,1369,1370][i - 977]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC1 (i : Nat) (hi : 1017 ≤ i) (hii : i ≤ 1056) :
    Artifact.submissionArtifact.instructionPC i =
      [1371,1372,1373,1375,1376,1377,1378,1379,1380,1381,1384,1385,1387,1388,1389,1390,1391,1392,1394,1395,1396,1399,1400,1401,1404,1405,1406,1409,1410,1411,1413,1414,1417,1418,1419,1421,1422,1423,1424,1427][i - 1017]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC2 (i : Nat) (hi : 1057 ≤ i) (hii : i ≤ 1096) :
    Artifact.submissionArtifact.instructionPC i =
      [1428,1429,1432,1433,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1453,1454,1455,1456,1458,1459,1460,1461,1462,1463,1465,1466,1467,1468,1469,1470,1472,1473,1474,1475][i - 1057]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC3 (i : Nat) (hi : 1097 ≤ i) (hii : i ≤ 1136) :
    Artifact.submissionArtifact.instructionPC i =
      [1476,1477,1479,1480,1481,1482,1483,1484,1486,1487,1488,1489,1490,1491,1493,1494,1495,1496,1497,1498,1500,1501,1502,1503,1504,1505,1507,1508,1509,1510,1511,1514,1515,1516,1517,1519,1522,1523,1526,1529][i - 1097]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC4 (i : Nat) (hi : 1137 ≤ i) (hii : i ≤ 1176) :
    Artifact.submissionArtifact.instructionPC i =
      [1532,1533,1534,1537,1538,1541,1544,1545,1548,1551,1554,1555,1556,1559,1560,1563,1566,1567,1569,1570,1573,1576,1579,1582,1585,1586,1587,1588,1589,1590,1592,1593,1596,1597,1600,1601,1604,1605,1606,1609][i - 1137]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC5 (i : Nat) (hi : 1177 ≤ i) (hii : i ≤ 1216) :
    Artifact.submissionArtifact.instructionPC i =
      [1612,1615,1616,1617,1618,1619,1622,1623,1625,1626,1627,1630,1631,1632,1633,1634,1635,1638,1639,1640,1642,1643,1645,1646,1647,1648,1650,1651,1652,1654,1655,1657,1658,1659,1660,1661,1664,1665,1666,1668][i - 1177]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC6 (i : Nat) (hi : 1217 ≤ i) (hii : i ≤ 1256) :
    Artifact.submissionArtifact.instructionPC i =
      [1669,1670,1671,1672,1673,1676,1677,1680,1683,1686,1689,1692,1693,1694,1695,1696,1697,1699,1700,1701,1702,1704,1705,1706,1707,1710,1711,1712,1715,1718,1721,1724,1727,1728,1729,1731,1732,1735,1736,1737][i - 1217]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC7 (i : Nat) (hi : 1257 ≤ i) (hii : i ≤ 1296) :
    Artifact.submissionArtifact.instructionPC i =
      [1738,1739,1742,1745,1748,1751,1754,1755,1756,1757,1760,1761,1764,1767,1768,1769,1770,1771,1772,1773,1774,1777,1778,1781,1782,1783,1784,1785,1786,1787,1789,1790,1793,1796,1799,1802,1805,1806,1807,1808][i - 1257]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC8 (i : Nat) (hi : 1297 ≤ i) (hii : i ≤ 1336) :
    Artifact.submissionArtifact.instructionPC i =
      [1809,1810,1811,1814,1815,1818,1821,1824,1827,1830,1831,1832,1833,1835,1836,1837,1840,1841,1842,1843,1845,1846,1849,1850,1851,1852,1854,1855,1858,1859,1860,1863,1866,1869,1872,1875,1876,1877,1878,1879][i - 1297]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC9 (i : Nat) (hi : 1337 ≤ i) (hii : i ≤ 1376) :
    Artifact.submissionArtifact.instructionPC i =
      [1880,1883,1884,1885,1886,1887,1888,1891,1892,1893,1894,1895,1896,1899,1900,1901,1902,1903,1904,1905,1906,1907,1910,1911,1912,1915,1916,1919,1920,1921,1922,1925,1926,1927,1929,1930,1931,1932,1935,1936][i - 1337]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC10 (i : Nat) (hi : 1377 ≤ i) (hii : i ≤ 1416) :
    Artifact.submissionArtifact.instructionPC i =
      [1937,1938,1939,1940,1943,1944,1945,1947,1948,1949,1952,1953,1954,1955,1956,1958,1959,1960,1962,1963,1964,1965,1966,1967,1968,1970,1971,1972,1973,1974,1975,1976,1977,1978,1981,1982,1983,1985,1986,1989][i - 1377]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC11 (i : Nat) (hi : 1417 ≤ i) (hii : i ≤ 1456) :
    Artifact.submissionArtifact.instructionPC i =
      [1990,1991,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2036,2037,2038,2039,2040,2041,2042,2043,2044,2045,2046,2047,2048,2049,2050,2051,2052,2053,2054,2055,2056,2057,2058,2059,2060,2061,2062][i - 1417]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC12 (i : Nat) (hi : 1457 ≤ i) (hii : i ≤ 1496) :
    Artifact.submissionArtifact.instructionPC i =
      [2063,2064,2097,2098,2099,2132,2133,2134,2135,2136,2137,2140,2141,2142,2143,2144,2147,2148,2149,2150,2153,2154,2155,2158,2159,2162,2163,2164,2167,2168,2169,2170,2173,2174,2175,2176,2177,2178,2179,2212][i - 1457]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC13 (i : Nat) (hi : 1497 ≤ i) (hii : i ≤ 1536) :
    Artifact.submissionArtifact.instructionPC i =
      [2213,2214,2215,2216,2217,2218,2219,2220,2221,2222,2223,2224,2225,2228,2229,2231,2232,2233,2236,2237,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2249,2282,2283,2284,2285,2286,2287,2288,2289,2290][i - 1497]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC14 (i : Nat) (hi : 1537 ≤ i) (hii : i ≤ 1576) :
    Artifact.submissionArtifact.instructionPC i =
      [2291,2292,2293,2294,2295,2296,2297,2298,2299,2300,2301,2302,2303,2304,2305,2306,2307,2308,2309,2311,2312,2313,2346,2347,2348,2381,2382,2383,2386,2387,2388,2391,2392,2393,2394,2395,2396,2397,2398,2399][i - 1537]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC15 (i : Nat) (hi : 1577 ≤ i) (hii : i ≤ 1616) :
    Artifact.submissionArtifact.instructionPC i =
      [2402,2403,2404,2405,2408,2409,2410,2413,2414,2415,2418,2419,2452,2453,2454,2455,2456,2459,2460,2461,2462,2463,2466,2467,2468,2471,2472,2473,2474,2475,2477,2478,2479,2480,2481,2482,2484,2485,2486,2487][i - 1577]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC16 (i : Nat) (hi : 1617 ≤ i) (hii : i ≤ 1656) :
    Artifact.submissionArtifact.instructionPC i =
      [2488,2489,2490,2491,2494,2495,2496,2497,2498,2499,2500,2501,2502,2503,2504,2505,2506,2507,2508,2509,2510,2511,2512,2513,2514,2515,2516,2517,2518,2519,2520,2553,2554,2555,2588,2589,2590,2591,2624,2625][i - 1617]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC17 (i : Nat) (hi : 1657 ≤ i) (hii : i ≤ 1696) :
    Artifact.submissionArtifact.instructionPC i =
      [2626,2629,2630,2631,2634,2635,2636,2637,2638,2641,2642,2643,2646,2647,2650,2651,2652,2655,2656,2659,2660,2661,2662,2663,2664,2665,2666,2667,2668,2669,2670,2671,2672,2673,2674,2675,2676,2677,2678,2679][i - 1657]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC18 (i : Nat) (hi : 1697 ≤ i) (hii : i ≤ 1736) :
    Artifact.submissionArtifact.instructionPC i =
      [2680,2681,2682,2683,2684,2685,2686,2687,2688,2689,2690,2691,2692,2725,2726,2727,2760,2761,2762,2763,2796,2797,2798,2801,2802,2803,2806,2807,2808,2809,2810,2811,2814,2815,2816,2849,2850,2853,2854,2857][i - 1697]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC19 (i : Nat) (hi : 1737 ≤ i) (hii : i ≤ 1741) :
    Artifact.submissionArtifact.instructionPC i =
      [2858,2859,2860,2861,2862][i - 1737]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC20 (i : Nat) (hi : 1742 ≤ i) (hii : i ≤ 1767) :
    Artifact.submissionArtifact.instructionPC i =
      [2863,2864,2867,2868,2869,2870,2873,2874,2875,2877,2878,2881,2882,2883,2884,2887,2888,2889,2891,2892,2893,2894,2897,2898,2899,2900][i - 1742]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC21 (i : Nat) (hi : 1768 ≤ i) (hii : i ≤ 1780) :
    Artifact.submissionArtifact.instructionPC i =
      [2901,2902,2903,2904,2906,2907,2908,2911,2912,2914,2917,2918,2921][i - 1768]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC22 (i : Nat) (hi : 1781 ≤ i) (hii : i ≤ 1815) :
    Artifact.submissionArtifact.instructionPC i =
      [2922,2923,2924,2927,2928,2929,2930,2931,2932,2933,2934,2937,2938,2940,2943,2944,2945,2946,2947,2949,2950,2951,2952,2954,2955,2956,2957,2959,2960,2961,2963,2964,2966,2967,2970][i - 1781]! := by
  interval_cases i <;> decide

@[simp] theorem fastPC23 (i : Nat) (hi : 1816 ≤ i) (hii : i ≤ 1830) :
    Artifact.submissionArtifact.instructionPC i =
      [2971,2972,2973,2976,2977,2980,2981,2984,2987,2988,2991,2994,2995,2996,2999][i - 1816]! := by
  interval_cases i <;> decide

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1196 = true :=
  Artifact.isValidJumpDest_index 899 (by rfl)

theorem jumpDest1533 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1533 = true :=
  Artifact.isValidJumpDest_index 1138 (by rfl)

theorem jumpDest1555 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1555 = true :=
  Artifact.isValidJumpDest_index 1148 (by rfl)

theorem jumpDest1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  Artifact.isValidJumpDest_index 1155 (by rfl)

theorem jumpDest1586 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1586 = true :=
  Artifact.isValidJumpDest_index 1162 (by rfl)

theorem jumpDest1615 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1615 = true :=
  Artifact.isValidJumpDest_index 1178 (by rfl)

theorem jumpDest1631 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1631 = true :=
  Artifact.isValidJumpDest_index 1189 (by rfl)

theorem jumpDest1668 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1668 = true :=
  Artifact.isValidJumpDest_index 1216 (by rfl)

theorem jumpDest1693 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1693 = true :=
  Artifact.isValidJumpDest_index 1229 (by rfl)

theorem jumpDest1728 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1728 = true :=
  Artifact.isValidJumpDest_index 1250 (by rfl)

theorem jumpDest1736 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1736 = true :=
  Artifact.isValidJumpDest_index 1255 (by rfl)

theorem jumpDest1755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1755 = true :=
  Artifact.isValidJumpDest_index 1264 (by rfl)

theorem jumpDest1756 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1756 = true :=
  Artifact.isValidJumpDest_index 1265 (by rfl)

theorem jumpDest1769 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1769 = true :=
  Artifact.isValidJumpDest_index 1272 (by rfl)

theorem jumpDest1789 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1789 = true :=
  Artifact.isValidJumpDest_index 1287 (by rfl)

theorem jumpDest1806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1806 = true :=
  Artifact.isValidJumpDest_index 1294 (by rfl)

theorem jumpDest1831 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1831 = true :=
  Artifact.isValidJumpDest_index 1307 (by rfl)

theorem jumpDest1832 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1832 = true :=
  Artifact.isValidJumpDest_index 1308 (by rfl)

theorem jumpDest1850 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1850 = true :=
  Artifact.isValidJumpDest_index 1320 (by rfl)

theorem jumpDest1876 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1876 = true :=
  Artifact.isValidJumpDest_index 1333 (by rfl)

theorem jumpDest1886 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1886 = true :=
  Artifact.isValidJumpDest_index 1341 (by rfl)

theorem jumpDest1892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1892 = true :=
  Artifact.isValidJumpDest_index 1345 (by rfl)

theorem jumpDest1900 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1900 = true :=
  Artifact.isValidJumpDest_index 1351 (by rfl)

theorem jumpDest1911 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1911 = true :=
  Artifact.isValidJumpDest_index 1360 (by rfl)

theorem jumpDest1915 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1915 = true :=
  Artifact.isValidJumpDest_index 1362 (by rfl)

theorem jumpDest1926 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1926 = true :=
  Artifact.isValidJumpDest_index 1369 (by rfl)

theorem jumpDest1939 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1939 = true :=
  Artifact.isValidJumpDest_index 1379 (by rfl)

theorem jumpDest1974 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1974 = true :=
  Artifact.isValidJumpDest_index 1406 (by rfl)

theorem jumpDest1995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1995 = true :=
  Artifact.isValidJumpDest_index 1421 (by rfl)

theorem jumpDest2241 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2241 = true :=
  Artifact.isValidJumpDest_index 1519 (by rfl)

theorem jumpDest2467 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2467 = true :=
  Artifact.isValidJumpDest_index 1600 (by rfl)

theorem jumpDest2500 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2500 = true :=
  Artifact.isValidJumpDest_index 1627 (by rfl)

theorem jumpDest2642 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2642 = true :=
  Artifact.isValidJumpDest_index 1667 (by rfl)

theorem jumpDest2666 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2666 = true :=
  Artifact.isValidJumpDest_index 1683 (by rfl)

theorem jumpDest2863 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2863 = true :=
  Artifact.isValidJumpDest_index 1742 (by rfl)

theorem jumpDest2874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2874 = true :=
  Artifact.isValidJumpDest_index 1749 (by rfl)

theorem jumpDest2877 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2877 = true :=
  Artifact.isValidJumpDest_index 1751 (by rfl)

theorem jumpDest2888 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2888 = true :=
  Artifact.isValidJumpDest_index 1758 (by rfl)

theorem jumpDest2901 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2901 = true :=
  Artifact.isValidJumpDest_index 1768 (by rfl)

theorem jumpDest2922 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2922 = true :=
  Artifact.isValidJumpDest_index 1781 (by rfl)

theorem jumpDest2944 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2944 = true :=
  Artifact.isValidJumpDest_index 1796 (by rfl)

theorem jumpDest2971 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2971 = true :=
  Artifact.isValidJumpDest_index 1816 (by rfl)

theorem jumpDest2995 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2995 = true :=
  Artifact.isValidJumpDest_index 1828 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
