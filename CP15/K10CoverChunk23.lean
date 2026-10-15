import CP15.K10CoverChunk22
import CP15.K10ModelCover

namespace CP15
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def k10p15chunk169Box : Certificate.ClosedBox 5 := ⟨![(87 / 50), (87 / 50), (123 / 100), (123 / 100), (123 / 100)], ![(9 / 4), (9 / 4), (9 / 4), (9 / 4), (9 / 4)]⟩
def k10p15chunk169Tree : K10ModelCover := (.split 2 (87 / 50) (.split 3 (87 / 50) (.split 4 (87 / 50) (.split 0 (399 / 200) (.split 1 (399 / 200) (.split 2 (297 / 200) (.split 3 (297 / 200) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 306), (.pair 2 3 303), (.pair 3 4 152), (.pair 4 0 311)]) (.split 4 (297 / 200) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 306), (.pair 2 3 152), (.pair 3 4 152), (.pair 4 0 306)]) (.split 0 (747 / 400) (.split 1 (747 / 400) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 318), (.pair 2 3 152), (.pair 3 4 1), (.pair 4 0 134)]) (.cycle 0 [(.support 0 1 54 53), (.pair 1 2 306), (.pair 2 3 152), (.pair 3 4 1), (.pair 4 0 134)])) (.split 1 (747 / 400) (.cycle 0 [(.support 0 1 53 54), (.pair 1 2 318), (.pair 2 3 152), (.pair 3 4 1), (.pair 4 0 311)]) (.outer ![53, 53, 0, 2, 2]))))) (.split 3 (297 / 200) (.split 4 (297 / 200) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 311), (.pair 2 3 152), (.pair 3 4 303), (.pair 4 0 306)]) (.split 0 (747 / 400) (.split 1 (747 / 400) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 134), (.pair 2 3 152), (.pair 3 4 152), (.pair 4 0 134)]) (.cycle 0 [(.support 0 1 54 53), (.pair 1 2 311), (.pair 2 3 152), (.pair 3 4 152), (.pair 4 0 134)])) (.cycle 0 [(.support 0 1 53 54), (.pair 1 2 311), (.pair 2 3 152), (.pair 3 4 152), (.pair 4 0 311)]))) (.split 4 (297 / 200) (.split 0 (747 / 400) (.split 1 (747 / 400) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 134), (.pair 2 3 1), (.pair 3 4 152), (.pair 4 0 318)]) (.cycle 0 [(.support 0 1 54 53), (.pair 1 2 311), (.pair 2 3 1), (.pair 3 4 152), (.pair 4 0 318)])) (.split 1 (747 / 400) (.cycle 0 [(.support 0 1 53 54), (.pair 1 2 134), (.pair 2 3 1), (.pair 3 4 152), (.pair 4 0 306)]) (.outer ![53, 53, 2, 2, 0]))) (.split 0 (747 / 400) (.split 1 (747 / 400) (.split 2 (129 / 80) (.split 3 (129 / 80) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 133), (.pair 2 3 153), (.pair 3 4 154), (.pair 4 0 134)]) (.split 4 (129 / 80) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 133), (.pair 2 3 154), (.pair 3 4 154), (.pair 4 0 133)]) (.split 0 (1443 / 800) (.split 1 (1443 / 800) (.split 2 (1239 / 800) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 400), (.pair 2 3 157), (.pair 3 4 1), (.pair 4 0 412)]) (.split 3 (1341 / 800) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 399), (.pair 2 3 161), (.pair 3 4 156), (.pair 4 0 412)]) (.split 4 (1341 / 800) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 399), (.pair 2 3 154), (.pair 3 4 156), (.pair 4 0 363)]) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 399), (.pair 2 3 154), (.pair 3 4 1), (.support 4 0 28 54)])))) (.split 2 (1239 / 800) (.cycle 0 [(.support 0 1 54 55), (.pair 1 2 398), (.pair 2 3 157), (.pair 3 4 1), (.pair 4 0 412)]) (.split 3 (1341 / 800) (.cycle 0 [(.support 0 1 54 55), (.pair 1 2 133), (.pair 2 3 161), (.pair 3 4 156), (.pair 4 0 412)]) (.split 4 (1341 / 800) (.cycle 0 [(.support 0 1 54 55), (.pair 1 2 133), (.pair 2 3 154), (.pair 3 4 156), (.pair 4 0 363)]) (.outer ![54, 55, 32, 28, 28]))))) (.cycle 0 [(.support 0 1 55 54), (.pair 1 2 133), (.pair 2 3 154), (.pair 3 4 1), (.support 4 0 31 55)])))) (.split 3 (129 / 80) (.split 4 (129 / 80) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 31), (.pair 2 3 154), (.pair 3 4 153), (.pair 4 0 133)]) (.split 0 (1443 / 800) (.split 1 (1443 / 800) (.split 2 (1341 / 800) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 363), (.pair 2 3 161), (.pair 3 4 154), (.pair 4 0 412)]) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 28), (.pair 2 3 154), (.pair 3 4 154), (.pair 4 0 412)])) (.cycle 0 [(.support 0 1 54 55), (.support 1 2 55 31), (.pair 2 3 154), (.pair 3 4 154), (.pair 4 0 412)])) (.cycle 0 [(.support 0 1 55 54), (.support 1 2 54 31), (.pair 2 3 154), (.pair 3 4 154), (.support 4 0 31 55)]))) (.split 4 (129 / 80) (.split 0 (1443 / 800) (.split 1 (1443 / 800) (.split 2 (1341 / 800) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 363), (.pair 2 3 156), (.pair 3 4 154), (.pair 4 0 399)]) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 28), (.pair 2 3 1), (.pair 3 4 154), (.pair 4 0 399)])) (.cycle 0 [(.support 0 1 54 55), (.support 1 2 55 31), (.pair 2 3 1), (.pair 3 4 154), (.pair 4 0 399)])) (.split 1 (1443 / 800) (.split 2 (1341 / 800) (.cycle 0 [(.support 0 1 55 54), (.pair 1 2 363), (.pair 2 3 156), (.pair 3 4 154), (.pair 4 0 133)]) (.cycle 0 [(.support 0 1 55 54), (.support 1 2 54 28), (.pair 2 3 1), (.pair 3 4 154), (.pair 4 0 133)])) (.cycle 0 [(.support 0 1 55 55), (.support 1 2 55 31), (.pair 2 3 1), (.pair 3 4 154), (.pair 4 0 133)]))) (.split 0 (1443 / 800) (.split 1 (1443 / 800) (.split 2 (1341 / 800) (.split 3 (1341 / 800) (.split 4 (1341 / 800) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 363), (.pair 2 3 162), (.pair 3 4 162), (.pair 4 0 363)]) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 363), (.pair 2 3 162), (.pair 3 4 156), (.support 4 0 28 54)])) (.split 4 (1341 / 800) (.split 0 (567 / 320) (.split 1 (567 / 320) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 483), (.pair 2 3 156), (.pair 3 4 156), (.pair 4 0 483)]) (.cycle 0 [(.support 0 1 54 63), (.pair 1 2 363), (.pair 2 3 156), (.pair 3 4 156), (.pair 4 0 483)])) (.split 1 (567 / 320) (.cycle 0 [(.support 0 1 63 54), (.pair 1 2 483), (.pair 2 3 156), (.pair 3 4 156), (.pair 4 0 363)]) (.cycle 0 [(.support 0 1 63 63), (.pair 1 2 363), (.pair 2 3 156), (.pair 3 4 156), (.pair 4 0 363)]))) (.split 0 (567 / 320) (.split 1 (567 / 320) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 483), (.pair 2 3 156), (.pair 3 4 1), (.support 4 0 28 54)]) (.cycle 0 [(.support 0 1 54 63), (.pair 1 2 363), (.pair 2 3 156), (.pair 3 4 1), (.support 4 0 28 54)])) (.cycle 0 [(.support 0 1 63 54), (.pair 1 2 363), (.pair 2 3 156), (.pair 3 4 1), (.support 4 0 28 63)])))) (.split 3 (1341 / 800) (.split 4 (1341 / 800) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 28), (.pair 2 3 156), (.pair 3 4 162), (.pair 4 0 363)]) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 28), (.pair 2 3 156), (.pair 3 4 156), (.support 4 0 28 54)])) (.split 4 (1341 / 800) (.split 0 (567 / 320) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 28), (.pair 2 3 1), (.pair 3 4 156), (.pair 4 0 483)]) (.cycle 0 [(.support 0 1 63 54), (.support 1 2 54 28), (.pair 2 3 1), (.pair 3 4 156), (.pair 4 0 363)])) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 28), (.pair 2 3 1), (.pair 3 4 1), (.support 4 0 28 54)])))) (.split 2 (1341 / 800) (.split 3 (1341 / 800) (.cycle 0 [(.support 0 1 54 55), (.support 1 2 55 31), (.pair 2 3 162), (.pair 3 4 156), (.pair 4 0 412)]) (.split 4 (1341 / 800) (.cycle 0 [(.support 0 1 54 55), (.support 1 2 55 31), (.pair 2 3 156), (.pair 3 4 156), (.pair 4 0 363)]) (.outer ![54, 55, 31, 28, 28]))) (.cycle 0 [(.support 0 1 54 55), (.support 1 2 55 28), (.pair 2 3 1), (.pair 3 4 1), (.pair 4 0 412)]))) (.split 1 (1443 / 800) (.split 2 (1341 / 800) (.cycle 0 [(.support 0 1 55 54), (.pair 1 2 363), (.pair 2 3 156), (.pair 3 4 1), (.support 4 0 31 55)]) (.cycle 0 [(.support 0 1 55 54), (.support 1 2 54 28), (.pair 2 3 1), (.pair 3 4 1), (.support 4 0 31 55)])) (.cycle 0 [(.support 0 1 55 55), (.support 1 2 55 31), (.pair 2 3 1), (.pair 3 4 1), (.support 4 0 31 55)])))))) (.split 2 (129 / 80) (.split 3 (129 / 80) (.cycle 0 [(.support 0 1 54 53), (.pair 1 2 348), (.pair 2 3 153), (.pair 3 4 154), (.pair 4 0 134)]) (.split 4 (129 / 80) (.cycle 0 [(.support 0 1 54 53), (.pair 1 2 348), (.pair 2 3 154), (.pair 3 4 154), (.pair 4 0 133)]) (.split 0 (1443 / 800) (.split 1 (309 / 160) (.split 2 (1239 / 800) (.cycle 0 [(.support 0 1 54 53), (.pair 1 2 352), (.pair 2 3 157), (.pair 3 4 1), (.pair 4 0 412)]) (.split 3 (1341 / 800) (.cycle 0 [(.support 0 1 54 53), (.pair 1 2 355), (.pair 2 3 161), (.pair 3 4 156), (.pair 4 0 412)]) (.outer ![54, 53, 32, 28, 31]))) (.outer ![54, 51, 2, 31, 31])) (.outer ![55, 53, 2, 31, 31])))) (.split 3 (129 / 80) (.cycle 0 [(.support 0 1 54 53), (.support 1 2 53 31), (.pair 2 3 154), (.pair 3 4 154), (.pair 4 0 134)]) (.split 4 (129 / 80) (.cycle 0 [(.support 0 1 54 53), (.support 1 2 53 31), (.pair 2 3 1), (.pair 3 4 154), (.pair 4 0 133)]) (.cycle 0 [(.support 0 1 54 53), (.support 1 2 53 31), (.pair 2 3 1), (.pair 3 4 1), (.support 4 0 31 54)]))))) (.split 1 (747 / 400) (.split 2 (129 / 80) (.split 3 (129 / 80) (.cycle 0 [(.support 0 1 53 54), (.pair 1 2 133), (.pair 2 3 153), (.pair 3 4 154), (.pair 4 0 311)]) (.cycle 3 [(.support 3 0 31 53), (.support 0 1 53 54), (.pair 1 2 133), (.pair 2 3 154)])) (.split 3 (129 / 80) (.split 4 (129 / 80) (.cycle 0 [(.support 0 1 53 54), (.support 1 2 54 31), (.pair 2 3 154), (.pair 3 4 153), (.pair 4 0 348)]) (.cycle 0 [(.support 0 1 53 54), (.support 1 2 54 31), (.pair 2 3 154), (.pair 3 4 154), (.support 4 0 31 53)])) (.split 4 (129 / 80) (.split 0 (309 / 160) (.split 1 (1443 / 800) (.split 2 (1341 / 800) (.cycle 0 [(.support 0 1 53 54), (.pair 1 2 363), (.pair 2 3 156), (.pair 3 4 154), (.pair 4 0 355)]) (.outer ![53, 54, 28, 31, 2])) (.outer ![53, 55, 31, 31, 2])) (.outer ![51, 54, 31, 31, 2])) (.cycle 0 [(.support 0 1 53 54), (.support 1 2 54 31), (.pair 2 3 1), (.pair 3 4 1), (.support 4 0 31 53)])))) (.outer ![53, 53, 2, 2, 2])))))) (.outer ![54, 49, 0, 0, 0])) (.outer ![49, 54, 0, 0, 0])) (.split 0 (399 / 200) (.split 1 (399 / 200) (.split 2 (297 / 200) (.split 3 (297 / 200) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 306), (.pair 2 3 303), (.pair 3 4 305), (.support 4 0 54 54)]) (.split 4 (399 / 200) (.split 0 (747 / 400) (.split 1 (747 / 400) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 318), (.pair 2 3 152), (.pair 3 4 311), (.support 4 0 54 54)]) (.outer ![54, 53, 0, 2, 54])) (.outer ![53, 54, 0, 2, 54])) (.outer ![54, 54, 0, 2, 49]))) (.split 3 (297 / 200) (.split 4 (399 / 200) (.split 0 (747 / 400) (.split 1 (747 / 400) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 134), (.pair 2 3 152), (.pair 3 4 306), (.support 4 0 54 54)]) (.outer ![54, 53, 2, 0, 54])) (.outer ![53, 54, 2, 0, 54])) (.outer ![54, 54, 2, 0, 49])) (.split 4 (399 / 200) (.split 0 (747 / 400) (.split 1 (747 / 400) (.split 2 (129 / 80) (.split 3 (129 / 80) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 133), (.pair 2 3 153), (.pair 3 4 348), (.support 4 0 54 54)]) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 133), (.pair 2 3 154), (.support 3 4 31 54), (.support 4 0 54 54)])) (.split 3 (129 / 80) (.split 4 (747 / 400) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 31), (.pair 2 3 154), (.pair 3 4 133), (.support 4 0 54 54)]) (.outer ![54, 54, 31, 2, 53])) (.split 4 (747 / 400) (.split 0 (1443 / 800) (.split 1 (1443 / 800) (.split 2 (1341 / 800) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 363), (.pair 2 3 156), (.support 3 4 31 54), (.support 4 0 54 54)]) (.outer ![54, 54, 28, 31, 54])) (.outer ![54, 55, 31, 31, 54])) (.outer ![55, 54, 31, 31, 54])) (.outer ![54, 54, 31, 31, 53])))) (.outer ![54, 53, 2, 2, 54])) (.outer ![53, 54, 2, 2, 54])) (.outer ![54, 54, 2, 2, 49])))) (.outer ![54, 49, 0, 0, 54])) (.outer ![49, 54, 0, 0, 54]))) (.split 4 (87 / 50) (.split 0 (399 / 200) (.split 1 (399 / 200) (.split 2 (297 / 200) (.split 3 (399 / 200) (.split 4 (297 / 200) (.split 0 (747 / 400) (.split 1 (747 / 400) (.split 2 (543 / 400) (.cycle 3 [(.support 3 0 54 54), (.support 0 1 54 54), (.pair 1 2 151), (.pair 2 3 317)]) (.split 3 (747 / 400) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 318), (.pair 2 3 318), (.pair 3 4 318), (.pair 4 0 318)]) (.outer ![54, 54, 5, 53, 0]))) (.outer ![54, 53, 0, 54, 0])) (.outer ![53, 54, 0, 54, 0])) (.split 0 (747 / 400) (.split 1 (747 / 400) (.split 2 (543 / 400) (.cycle 3 [(.support 3 0 54 54), (.support 0 1 54 54), (.pair 1 2 151), (.pair 2 3 317)]) (.split 3 (747 / 400) (.cycle 3 [(.support 3 0 54 54), (.support 0 1 54 54), (.pair 1 2 318), (.pair 2 3 318)]) (.outer ![54, 54, 5, 53, 2]))) (.outer ![54, 53, 0, 54, 2])) (.outer ![53, 54, 0, 54, 2]))) (.outer ![54, 54, 0, 49, 0])) (.split 3 (399 / 200) (.split 4 (297 / 200) (.split 0 (747 / 400) (.split 1 (747 / 400) (.split 2 (129 / 80) (.split 3 (747 / 400) (.cycle 4 [(.pair 4 0 318), (.support 0 1 54 54), (.support 1 3 54 54), (.pair 3 4 318)]) (.outer ![54, 54, 2, 53, 0])) (.split 3 (747 / 400) (.cycle 4 [(.pair 4 0 318), (.support 0 1 54 54), (.support 1 3 54 54), (.pair 3 4 318)]) (.outer ![54, 54, 31, 53, 0]))) (.outer ![54, 53, 2, 54, 0])) (.outer ![53, 54, 2, 54, 0])) (.split 0 (747 / 400) (.split 1 (747 / 400) (.split 2 (129 / 80) (.split 3 (747 / 400) (.split 4 (129 / 80) (.split 0 (1443 / 800) (.split 1 (1443 / 800) (.split 2 (1239 / 800) (.cycle 3 [(.support 3 0 54 54), (.support 0 1 54 54), (.pair 1 2 400), (.pair 2 3 398)]) (.split 3 (1443 / 800) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 399), (.pair 2 3 399), (.pair 3 4 399), (.pair 4 0 399)]) (.outer ![54, 54, 32, 55, 2]))) (.outer ![54, 55, 2, 54, 2])) (.outer ![55, 54, 2, 54, 2])) (.split 0 (1443 / 800) (.split 1 (1443 / 800) (.split 2 (1239 / 800) (.cycle 3 [(.support 3 0 54 54), (.support 0 1 54 54), (.pair 1 2 400), (.pair 2 3 398)]) (.split 3 (1443 / 800) (.split 4 (1341 / 800) (.split 0 (567 / 320) (.split 1 (567 / 320) (.cycle 3 [(.support 3 0 54 54), (.support 0 1 54 54), (.pair 1 2 481), (.pair 2 3 399)]) (.outer ![54, 63, 32, 54, 31])) (.outer ![63, 54, 32, 54, 31])) (.outer ![54, 54, 32, 54, 28])) (.outer ![54, 54, 32, 55, 31]))) (.outer ![54, 55, 2, 54, 31])) (.outer ![55, 54, 2, 54, 31]))) (.outer ![54, 54, 2, 53, 2])) (.split 3 (747 / 400) (.split 4 (129 / 80) (.split 0 (1443 / 800) (.split 1 (1443 / 800) (.split 2 (1341 / 800) (.split 3 (1443 / 800) (.split 4 (1239 / 800) (.cycle 4 [(.pair 4 0 400), (.support 0 1 54 54), (.support 1 3 54 54), (.pair 3 4 400)]) (.split 0 (567 / 320) (.cycle 4 [(.pair 4 0 481), (.support 0 1 54 54), (.support 1 3 54 54), (.pair 3 4 399)]) (.outer ![63, 54, 31, 54, 32]))) (.outer ![54, 54, 31, 55, 2])) (.outer ![54, 54, 28, 54, 2])) (.outer ![54, 55, 31, 54, 2])) (.outer ![55, 54, 31, 54, 2])) (.split 0 (1443 / 800) (.split 1 (1443 / 800) (.split 2 (1341 / 800) (.split 3 (1443 / 800) (.split 4 (1341 / 800) (.split 0 (567 / 320) (.split 1 (567 / 320) (.split 2 (2631 / 1600) (.split 3 (567 / 320) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 480), (.pair 2 3 480), (.pair 3 4 483), (.pair 4 0 483)]) (.outer ![54, 54, 31, 63, 31])) (.split 3 (567 / 320) (.split 4 (2631 / 1600) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 483), (.pair 2 3 483), (.pair 3 4 480), (.pair 4 0 480)]) (.split 0 (5619 / 3200) (.split 1 (5619 / 3200) (.split 2 (5313 / 3200) (.cycle 0 [(.support 0 1 54 54), (.pair 1 2 502), (.pair 2 3 493), (.pair 3 4 483), (.pair 4 0 505)]) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 35), (.support 2 3 35 54), (.pair 3 4 483), (.pair 4 0 505)])) (.cycle 0 [(.support 0 1 54 66), (.support 1 2 66 30), (.pair 2 3 483), (.pair 3 4 483), (.pair 4 0 505)])) (.split 1 (5619 / 3200) (.cycle 0 [(.support 0 1 66 54), (.pair 1 2 505), (.pair 2 3 483), (.pair 3 4 483), (.support 4 0 30 66)]) (.outer ![66, 66, 30, 54, 30])))) (.outer ![54, 54, 30, 63, 31]))) (.outer ![54, 63, 31, 54, 31])) (.outer ![63, 54, 31, 54, 31])) (.outer ![54, 54, 31, 54, 28])) (.outer ![54, 54, 31, 55, 31])) (.outer ![54, 54, 28, 54, 31])) (.outer ![54, 55, 31, 54, 31])) (.outer ![55, 54, 31, 54, 31]))) (.outer ![54, 54, 31, 53, 2]))) (.outer ![54, 53, 2, 54, 2])) (.outer ![53, 54, 2, 54, 2]))) (.outer ![54, 54, 2, 49, 0]))) (.outer ![54, 49, 0, 54, 0])) (.outer ![49, 54, 0, 54, 0])) (.outer ![54, 54, 0, 54, 54]))) (.split 3 (87 / 50) (.split 4 (87 / 50) (.split 0 (399 / 200) (.split 1 (399 / 200) (.split 2 (399 / 200) (.split 3 (297 / 200) (.split 4 (297 / 200) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 54), (.pair 2 3 306), (.pair 3 4 303), (.pair 4 0 306)]) (.split 0 (747 / 400) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 54), (.pair 2 3 306), (.pair 3 4 152), (.pair 4 0 134)]) (.outer ![53, 54, 54, 0, 2]))) (.split 4 (297 / 200) (.split 0 (747 / 400) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 54), (.pair 2 3 311), (.pair 3 4 152), (.pair 4 0 318)]) (.outer ![53, 54, 54, 2, 0])) (.split 0 (747 / 400) (.split 1 (747 / 400) (.split 2 (747 / 400) (.split 3 (129 / 80) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 54), (.pair 2 3 133), (.pair 3 4 154), (.pair 4 0 134)]) (.split 4 (129 / 80) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 54), (.support 2 3 54 31), (.pair 3 4 154), (.pair 4 0 133)]) (.split 0 (1443 / 800) (.split 1 (1443 / 800) (.split 2 (1443 / 800) (.split 3 (1341 / 800) (.cycle 0 [(.support 0 1 54 54), (.support 1 2 54 54), (.pair 2 3 363), (.pair 3 4 156), (.pair 4 0 412)]) (.outer ![54, 54, 54, 28, 31])) (.outer ![54, 54, 55, 31, 31])) (.outer ![54, 55, 54, 31, 31])) (.outer ![55, 54, 54, 31, 31])))) (.outer ![54, 54, 53, 2, 2])) (.outer ![54, 53, 54, 2, 2])) (.outer ![53, 54, 54, 2, 2])))) (.outer ![54, 54, 49, 0, 0])) (.outer ![54, 49, 54, 0, 0])) (.outer ![49, 54, 54, 0, 0])) (.outer ![54, 54, 54, 0, 54])) (.outer ![54, 54, 54, 54, 0])))

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk169Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk169Box k10p15chunk169Tree = true := by
  apply k10ModelCoverCheck_split_true
  · apply k10ModelCoverCheck_split_true
    · apply k10ModelCoverCheck_split_true
      · apply k10ModelCoverCheck_split_true
        · apply k10ModelCoverCheck_split_true
          · apply k10ModelCoverCheck_split_true
            · apply k10ModelCoverCheck_split_true
              · decide +kernel
              · apply k10ModelCoverCheck_split_true
                · decide +kernel
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · decide +kernel
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · decide +kernel
            · apply k10ModelCoverCheck_split_true
              · apply k10ModelCoverCheck_split_true
                · decide +kernel
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · decide +kernel
                  · decide +kernel
              · apply k10ModelCoverCheck_split_true
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · decide +kernel
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · decide +kernel
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · apply k10ModelCoverCheck_split_true
                                  · decide +kernel
                                  · apply k10ModelCoverCheck_split_true
                                    · decide +kernel
                                    · decide +kernel
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · apply k10ModelCoverCheck_split_true
                                  · decide +kernel
                                  · apply k10ModelCoverCheck_split_true
                                    · decide +kernel
                                    · decide +kernel
                            · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
                              · decide +kernel
                            · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
                              · decide +kernel
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
                              · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · apply k10ModelCoverCheck_split_true
                                  · apply k10ModelCoverCheck_split_true
                                    · decide +kernel
                                    · decide +kernel
                                  · apply k10ModelCoverCheck_split_true
                                    · apply k10ModelCoverCheck_split_true
                                      · apply k10ModelCoverCheck_split_true
                                        · decide +kernel
                                        · decide +kernel
                                      · apply k10ModelCoverCheck_split_true
                                        · decide +kernel
                                        · decide +kernel
                                    · apply k10ModelCoverCheck_split_true
                                      · apply k10ModelCoverCheck_split_true
                                        · decide +kernel
                                        · decide +kernel
                                      · decide +kernel
                                · apply k10ModelCoverCheck_split_true
                                  · apply k10ModelCoverCheck_split_true
                                    · decide +kernel
                                    · decide +kernel
                                  · apply k10ModelCoverCheck_split_true
                                    · apply k10ModelCoverCheck_split_true
                                      · decide +kernel
                                      · decide +kernel
                                    · decide +kernel
                              · apply k10ModelCoverCheck_split_true
                                · apply k10ModelCoverCheck_split_true
                                  · decide +kernel
                                  · apply k10ModelCoverCheck_split_true
                                    · decide +kernel
                                    · decide +kernel
                                · decide +kernel
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
                              · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · apply k10ModelCoverCheck_split_true
                                  · decide +kernel
                                  · decide +kernel
                              · decide +kernel
                            · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
                              · decide +kernel
                            · decide +kernel
                          · decide +kernel
                    · decide +kernel
          · decide +kernel
        · decide +kernel
      · apply k10ModelCoverCheck_split_true
        · apply k10ModelCoverCheck_split_true
          · apply k10ModelCoverCheck_split_true
            · apply k10ModelCoverCheck_split_true
              · decide +kernel
              · apply k10ModelCoverCheck_split_true
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · decide +kernel
                  · decide +kernel
                · decide +kernel
            · apply k10ModelCoverCheck_split_true
              · apply k10ModelCoverCheck_split_true
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · decide +kernel
                  · decide +kernel
                · decide +kernel
              · apply k10ModelCoverCheck_split_true
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
                              · decide +kernel
                            · decide +kernel
                          · decide +kernel
                    · decide +kernel
                  · decide +kernel
                · decide +kernel
          · decide +kernel
        · decide +kernel
    · apply k10ModelCoverCheck_split_true
      · apply k10ModelCoverCheck_split_true
        · apply k10ModelCoverCheck_split_true
          · apply k10ModelCoverCheck_split_true
            · apply k10ModelCoverCheck_split_true
              · apply k10ModelCoverCheck_split_true
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · decide +kernel
                    · decide +kernel
                  · decide +kernel
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · decide +kernel
                    · decide +kernel
                  · decide +kernel
              · decide +kernel
            · apply k10ModelCoverCheck_split_true
              · apply k10ModelCoverCheck_split_true
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · decide +kernel
                    · decide +kernel
                  · decide +kernel
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · apply k10ModelCoverCheck_split_true
                                  · decide +kernel
                                  · decide +kernel
                              · decide +kernel
                            · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · apply k10ModelCoverCheck_split_true
                                  · apply k10ModelCoverCheck_split_true
                                    · apply k10ModelCoverCheck_split_true
                                      · apply k10ModelCoverCheck_split_true
                                        · decide +kernel
                                        · decide +kernel
                                      · decide +kernel
                                    · decide +kernel
                                  · decide +kernel
                              · decide +kernel
                            · decide +kernel
                        · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · apply k10ModelCoverCheck_split_true
                                  · apply k10ModelCoverCheck_split_true
                                    · decide +kernel
                                    · apply k10ModelCoverCheck_split_true
                                      · decide +kernel
                                      · decide +kernel
                                  · decide +kernel
                                · decide +kernel
                              · decide +kernel
                            · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · apply k10ModelCoverCheck_split_true
                                  · apply k10ModelCoverCheck_split_true
                                    · apply k10ModelCoverCheck_split_true
                                      · apply k10ModelCoverCheck_split_true
                                        · apply k10ModelCoverCheck_split_true
                                          · apply k10ModelCoverCheck_split_true
                                            · decide +kernel
                                            · decide +kernel
                                          · apply k10ModelCoverCheck_split_true
                                            · apply k10ModelCoverCheck_split_true
                                              · decide +kernel
                                              · apply k10ModelCoverCheck_split_true
                                                · apply k10ModelCoverCheck_split_true
                                                  · apply k10ModelCoverCheck_split_true
                                                    · decide +kernel
                                                    · decide +kernel
                                                  · decide +kernel
                                                · apply k10ModelCoverCheck_split_true
                                                  · decide +kernel
                                                  · decide +kernel
                                            · decide +kernel
                                        · decide +kernel
                                      · decide +kernel
                                    · decide +kernel
                                  · decide +kernel
                                · decide +kernel
                              · decide +kernel
                            · decide +kernel
                        · decide +kernel
                    · decide +kernel
                  · decide +kernel
              · decide +kernel
          · decide +kernel
        · decide +kernel
      · decide +kernel
  · apply k10ModelCoverCheck_split_true
    · apply k10ModelCoverCheck_split_true
      · apply k10ModelCoverCheck_split_true
        · apply k10ModelCoverCheck_split_true
          · apply k10ModelCoverCheck_split_true
            · apply k10ModelCoverCheck_split_true
              · apply k10ModelCoverCheck_split_true
                · decide +kernel
                · apply k10ModelCoverCheck_split_true
                  · decide +kernel
                  · decide +kernel
              · apply k10ModelCoverCheck_split_true
                · apply k10ModelCoverCheck_split_true
                  · decide +kernel
                  · decide +kernel
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · apply k10ModelCoverCheck_split_true
                                  · decide +kernel
                                  · decide +kernel
                                · decide +kernel
                              · decide +kernel
                            · decide +kernel
                      · decide +kernel
                    · decide +kernel
                  · decide +kernel
            · decide +kernel
          · decide +kernel
        · decide +kernel
      · decide +kernel
    · decide +kernel


def k10p15chunk170Box : Certificate.ClosedBox 5 := ⟨![(87 / 50), (123 / 100), (123 / 100), (123 / 100), (123 / 100)], ![(9 / 4), (9 / 4), (9 / 4), (9 / 4), (9 / 4)]⟩
def k10p15chunk170Tree : K10ModelCover := (.split 1 (87 / 50) k10p15chunk168Tree k10p15chunk169Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk170Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk170Box k10p15chunk170Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk170Box.left 1 (87 / 50)) = k10p15chunk168Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk170Box k10p15chunk168Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk168Checked
  · have heq : k10CachedBox (k10p15chunk170Box.right 1 (87 / 50)) = k10p15chunk169Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk170Box k10p15chunk169Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk169Checked


def k10p15chunk171Box : Certificate.ClosedBox 5 := ⟨![(123 / 100), (123 / 100), (123 / 100), (123 / 100), (123 / 100)], ![(9 / 4), (9 / 4), (9 / 4), (9 / 4), (9 / 4)]⟩
def k10p15chunk171Tree : K10ModelCover := (.split 0 (87 / 50) k10p15chunk139Tree k10p15chunk170Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk171Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk171Box k10p15chunk171Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk171Box.left 0 (87 / 50)) = k10p15chunk139Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk171Box k10p15chunk139Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk139Checked
  · have heq : k10CachedBox (k10p15chunk171Box.right 0 (87 / 50)) = k10p15chunk170Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk171Box k10p15chunk170Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk170Checked


end CP15
