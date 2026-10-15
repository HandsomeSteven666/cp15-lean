import CP15.K10CoverChunk5
import CP15.K10ModelCover

namespace CP15
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def k10p15chunk33Box : Certificate.ClosedBox 5 := ⟨![(2733 / 1600), (1341 / 800), (1341 / 800), (1341 / 800), (1341 / 800)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk33Tree : K10ModelCover := (.split 1 (2733 / 1600) (.split 2 (2733 / 1600) (.split 3 (2733 / 1600) (.split 4 (2733 / 1600) (.split 0 (5517 / 3200) (.split 1 (1083 / 640) (.split 2 (1083 / 640) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.inner ![185, 222, 222, 222, 185]) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 222), (.pair 2 3 222), (.pair 3 4 192), (.support 4 0 37 27)])) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.inner ![201, 222, 192, 192, 201]) (.split 1 (10779 / 6400) (.inner ![200, 228, 192, 192, 185]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 222), (.pair 2 3 192), (.pair 3 4 192), (.pair 4 0 185)]))) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 228), (.pair 2 3 192), (.pair 3 4 170), (.support 4 0 37 27)]) (.split 2 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 228), (.pair 2 3 227), (.pair 3 4 170), (.support 4 0 37 27)]) .local)) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 222), (.pair 2 3 192), (.pair 3 4 170), (.support 4 0 37 41)])))) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.inner ![201, 192, 192, 222, 201]) (.split 1 (10779 / 6400) (.inner ![200, 227, 192, 222, 185]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 192), (.pair 2 3 192), (.pair 3 4 222), (.pair 4 0 185)]))) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 227), (.pair 2 3 192), (.pair 3 4 192), (.support 4 0 37 27)]) (.split 2 (10881 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 223), (.pair 2 3 223), (.pair 3 4 192), (.support 4 0 37 27)]) (.split 3 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 192), (.pair 2 3 227), (.pair 3 4 227), (.support 4 0 37 27)]) .local))) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 192), (.pair 2 3 192), (.pair 3 4 192), (.support 4 0 37 41)]))) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (10881 / 6400) (.inner ![230, 226, 195, 192, 201]) (.split 3 (10881 / 6400) (.inner ![230, 227, 195, 223, 201]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 227), (.support 2 3 39 39), (.pair 3 4 192), (.pair 4 0 201)]))) (.split 2 (10881 / 6400) (.split 3 (10881 / 6400) (.inner ![201, 223, 225, 223, 201]) (.split 4 (10779 / 6400) (.inner ![201, 223, 195, 227, 230]) .local)) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.inner ![201, 192, 195, 226, 230]) .local) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 192), (.support 2 3 39 39), (.pair 3 4 227), (.pair 4 0 230)]) .local)))) (.split 1 (10779 / 6400) (.split 2 (10881 / 6400) (.split 3 (10881 / 6400) (.inner ![200, 226, 225, 223, 185]) (.split 4 (10779 / 6400) (.inner ![200, 226, 195, 227, 200]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 226), (.pair 2 3 195), (.pair 3 4 192), (.support 4 0 40 41)]))) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.inner ![200, 227, 195, 226, 200]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 227), (.pair 2 3 195), (.pair 3 4 223), (.support 4 0 40 41)])) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 227), (.support 2 3 39 39), (.pair 3 4 227), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21507 / 12800) (.cycle 0 [(.pair 0 1 293), (.pair 1 2 235), (.support 2 3 39 39), (.pair 3 4 192), (.support 4 0 40 41)]) (.split 2 (21813 / 12800) (.cycle 0 [(.pair 0 1 270), (.pair 1 2 238), (.support 2 3 39 39), (.pair 3 4 192), (.support 4 0 40 41)]) (.cycle 0 [(.pair 0 1 270), (.pair 1 2 227), (.support 2 3 43 39), (.pair 3 4 192), (.support 4 0 40 41)]))) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 227), (.support 2 3 39 39), (.pair 3 4 192), (.support 4 0 40 46)]))))) (.split 2 (10881 / 6400) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 223), (.pair 2 3 225), (.pair 3 4 223), (.pair 4 0 185)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 223), (.pair 2 3 195), (.pair 3 4 227), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (21711 / 12800) (.inner ![262, 243, 247, 192, 265]) (.split 3 (21813 / 12800) (.inner ![262, 250, 252, 240, 265]) (.split 4 (21609 / 12800) (.inner ![262, 250, 195, 244, 262]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 250), (.support 2 3 44 43), (.pair 3 4 192), (.support 4 0 45 41)])))) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 223), (.pair 2 3 195), (.pair 3 4 192), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 223), (.pair 2 3 195), (.pair 3 4 192), (.support 4 0 40 46)])))) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 192), (.pair 2 3 195), (.pair 3 4 226), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (21813 / 12800) (.inner ![262, 251, 252, 223, 265]) (.split 3 (21711 / 12800) (.inner ![262, 244, 247, 248, 265]) (.split 4 (21609 / 12800) (.inner ![262, 244, 195, 250, 262]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 244), (.support 2 3 43 44), (.pair 3 4 223), (.support 4 0 45 41)])))) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 192), (.pair 2 3 195), (.pair 3 4 223), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 192), (.pair 2 3 195), (.pair 3 4 223), (.support 4 0 40 46)]))) (.split 4 (10779 / 6400) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 244), (.support 2 3 39 39), (.pair 3 4 227), (.pair 4 0 270)]) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 192), (.support 2 3 39 39), (.pair 3 4 227), (.pair 4 0 270)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 192), (.support 2 3 39 39), (.pair 3 4 227), (.pair 4 0 200)])) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (21813 / 12800) (.split 3 (21813 / 12800) (.split 4 (21609 / 12800) (.inner ![262, 251, 239, 251, 262]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 251), (.support 2 3 39 39), (.pair 3 4 240), (.support 4 0 45 41)])) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 251), (.support 2 3 39 43), (.pair 3 4 192), (.support 4 0 40 41)])) (.split 3 (21813 / 12800) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 244), (.support 2 3 43 39), (.pair 3 4 240), (.support 4 0 40 41)]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 244), (.support 2 3 43 43), (.pair 3 4 192), (.support 4 0 40 41)]))) (.split 2 (21813 / 12800) (.split 3 (21813 / 12800) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 240), (.support 2 3 39 39), (.pair 3 4 240), (.support 4 0 40 41)]) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 240), (.support 2 3 39 43), (.pair 3 4 192), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 192), (.support 2 3 43 39), (.pair 3 4 192), (.support 4 0 40 41)]))) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 192), (.support 2 3 39 39), (.pair 3 4 192), (.support 4 0 40 46)]))))))) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (10881 / 6400) (.split 3 (10881 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 226), (.pair 2 3 225), (.pair 3 4 195), (.support 4 0 37 27)]) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 226), (.pair 2 3 195), (.pair 3 4 195), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 226), (.pair 2 3 195), (.support 3 4 39 39), (.support 4 0 39 27)]))) (.split 3 (10881 / 6400) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 227), (.pair 2 3 195), (.pair 3 4 225), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 227), (.pair 2 3 195), (.pair 3 4 195), (.support 4 0 39 27)])) (.split 4 (10881 / 6400) (.split 0 (4383 / 2560) (.cycle 0 [(.pair 0 1 277), (.pair 1 2 227), (.support 2 3 39 39), (.pair 3 4 195), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 227), (.support 2 3 39 39), (.pair 3 4 195), (.support 4 0 37 47)])) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 227), (.support 2 3 39 39), (.support 3 4 39 39), (.support 4 0 39 27)])))) .local) (.split 1 (10779 / 6400) (.split 2 (10881 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 226), (.pair 2 3 195), (.pair 3 4 170), (.support 4 0 37 41)]) (.split 3 (10881 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 227), (.pair 2 3 195), (.pair 3 4 195), (.support 4 0 37 41)]) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 227), (.support 2 3 39 39), (.pair 3 4 195), (.support 4 0 37 41)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 227), (.support 2 3 39 39), (.support 3 4 39 39), (.support 4 0 39 41)])))) (.split 2 (10881 / 6400) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 223), (.pair 2 3 225), (.pair 3 4 195), (.support 4 0 37 41)]) (.split 4 (10881 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 223), (.pair 2 3 195), (.pair 3 4 195), (.support 4 0 37 41)]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 223), (.pair 2 3 195), (.support 3 4 39 39), (.support 4 0 39 41)]))) (.split 3 (10881 / 6400) (.split 4 (10881 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 192), (.pair 2 3 195), (.pair 3 4 225), (.support 4 0 37 41)]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 192), (.pair 2 3 195), (.pair 3 4 195), (.support 4 0 39 41)])) (.split 4 (10881 / 6400) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (21813 / 12800) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 251), (.support 2 3 39 39), (.pair 3 4 195), (.support 4 0 37 41)]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 244), (.support 2 3 43 39), (.pair 3 4 195), (.support 4 0 37 41)])) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 192), (.support 2 3 39 39), (.pair 3 4 195), (.support 4 0 37 41)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 192), (.support 2 3 39 39), (.pair 3 4 195), (.support 4 0 37 46)])) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 192), (.support 2 3 39 39), (.support 3 4 39 39), (.support 4 0 39 41)]))))))))) (.split 2 (1083 / 640) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 192), (.pair 2 3 222), (.pair 3 4 222), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 192), (.pair 2 3 222), (.pair 3 4 192), (.support 4 0 37 27)])) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 223), (.pair 2 3 192), (.pair 3 4 192), (.pair 4 0 201)]) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 192), (.pair 2 3 192), (.pair 3 4 192), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 192), (.pair 2 3 192), (.pair 3 4 192), (.pair 4 0 185)])) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 226), (.pair 2 3 227), (.pair 3 4 170), (.support 4 0 37 27)]) .local) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 227), (.pair 2 3 227), (.pair 3 4 170), (.support 4 0 37 27)]) .local)) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 192), (.pair 2 3 192), (.pair 3 4 170), (.support 4 0 37 41)])))) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 195), (.pair 2 3 192), (.pair 3 4 222), (.pair 4 0 201)]) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 170), (.pair 2 3 192), (.pair 3 4 222), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 170), (.pair 2 3 192), (.pair 3 4 222), (.pair 4 0 185)])) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 225), (.pair 2 3 223), (.pair 3 4 192), (.support 4 0 37 27)]) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 195), (.pair 2 3 227), (.pair 3 4 227), (.support 4 0 37 27)]) .local)) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 195), (.pair 2 3 223), (.pair 3 4 192), (.support 4 0 37 27)]) (.cycle 0 [(.support 0 1 27 39), (.support 1 2 39 39), (.pair 2 3 192), (.pair 3 4 192), (.support 4 0 37 27)]))) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 170), (.pair 2 3 192), (.pair 3 4 192), (.support 4 0 37 41)]))) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10881 / 6400) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 225), (.pair 2 3 225), (.pair 3 4 223), (.pair 4 0 201)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 225), (.pair 2 3 195), (.pair 3 4 227), (.pair 4 0 230)]) .local)) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 195), (.pair 2 3 195), (.pair 3 4 226), (.pair 4 0 230)]) .local) (.split 4 (10779 / 6400) (.split 0 (4383 / 2560) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 195), (.support 2 3 39 39), (.pair 3 4 227), (.pair 4 0 277)]) (.cycle 0 [(.support 0 1 47 37), (.pair 1 2 195), (.support 2 3 39 39), (.pair 3 4 227), (.pair 4 0 230)])) .local))) (.split 2 (10881 / 6400) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 195), (.pair 2 3 225), (.pair 3 4 223), (.pair 4 0 201)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 195), (.pair 2 3 195), (.pair 3 4 227), (.pair 4 0 230)]) .local)) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 27 39), (.support 1 2 39 39), (.pair 2 3 195), (.pair 3 4 223), (.pair 4 0 201)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 39), (.support 1 2 39 39), (.support 2 3 39 39), (.pair 3 4 227), (.pair 4 0 230)]) .local)))) (.split 1 (10881 / 6400) (.split 2 (10881 / 6400) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 225), (.pair 2 3 225), (.pair 3 4 223), (.pair 4 0 185)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 225), (.pair 2 3 195), (.pair 3 4 227), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 225), (.pair 2 3 195), (.pair 3 4 192), (.support 4 0 40 41)]))) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 195), (.pair 2 3 195), (.pair 3 4 226), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 195), (.pair 2 3 195), (.pair 3 4 223), (.support 4 0 40 41)])) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 195), (.support 2 3 39 39), (.pair 3 4 227), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21711 / 12800) (.split 2 (21813 / 12800) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 261), (.support 2 3 39 39), (.pair 3 4 192), (.support 4 0 40 41)]) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 247), (.support 2 3 43 39), (.pair 3 4 192), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 44), (.pair 1 2 195), (.support 2 3 39 39), (.pair 3 4 192), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 46 37), (.pair 1 2 195), (.support 2 3 39 39), (.pair 3 4 192), (.support 4 0 40 46)]))))) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 41 39), (.pair 1 2 195), (.pair 2 3 195), (.pair 3 4 192), (.pair 4 0 185)]) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 41 39), (.support 1 2 39 39), (.pair 2 3 195), (.pair 3 4 223), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 41 39), (.support 1 2 39 39), (.support 2 3 39 39), (.pair 3 4 192), (.pair 4 0 185)]))))) (.split 0 (10983 / 6400) .local (.split 1 (10881 / 6400) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 225), (.pair 2 3 195), (.pair 3 4 170), (.support 4 0 37 41)]) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 195), (.pair 2 3 195), (.pair 3 4 195), (.support 4 0 37 41)]) (.split 4 (10881 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 195), (.support 2 3 39 39), (.pair 3 4 195), (.support 4 0 37 41)]) (.outer ![41, 37, 39, 39, 39])))) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 41 39), (.pair 1 2 195), (.pair 2 3 195), (.pair 3 4 170), (.support 4 0 37 41)]) (.cycle 0 [(.support 0 1 41 39), (.support 1 2 39 39), (.pair 2 3 170), (.pair 3 4 170), (.support 4 0 37 41)])))))))) (.split 1 (1083 / 640) (.split 2 (1083 / 640) (.split 3 (1083 / 640) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 222), (.pair 2 3 222), (.pair 3 4 192), (.support 4 0 28 36)]) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 222), (.pair 2 3 192), (.pair 3 4 192), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 222), (.pair 2 3 192), (.pair 3 4 170), (.support 4 0 37 36)]))) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 192), (.pair 2 3 192), (.pair 3 4 222), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 192), (.pair 2 3 192), (.pair 3 4 192), (.support 4 0 37 36)])) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (10881 / 6400) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 226), (.pair 2 3 225), (.pair 3 4 223), (.support 4 0 28 36)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 226), (.pair 2 3 195), (.pair 3 4 227), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 226), (.pair 2 3 195), (.pair 3 4 192), (.support 4 0 40 36)]))) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 227), (.pair 2 3 195), (.pair 3 4 226), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 227), (.pair 2 3 195), (.pair 3 4 223), (.support 4 0 40 36)])) (.split 4 (10779 / 6400) (.split 0 (22119 / 12800) (.split 1 (21507 / 12800) (.cycle 0 [(.pair 0 1 287), (.pair 1 2 235), (.support 2 3 39 39), (.pair 3 4 227), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 42), (.pair 1 2 227), (.support 2 3 39 39), (.pair 3 4 227), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 48 28), (.pair 1 2 227), (.support 2 3 39 39), (.pair 3 4 227), (.support 4 0 28 48)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 227), (.support 2 3 39 39), (.pair 3 4 192), (.support 4 0 40 36)])))) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 223), (.pair 2 3 195), (.pair 3 4 192), (.support 4 0 28 36)]) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 192), (.pair 2 3 195), (.pair 3 4 223), (.support 4 0 28 36)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 192), (.support 2 3 39 39), (.pair 3 4 227), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 192), (.support 2 3 39 39), (.pair 3 4 192), (.support 4 0 40 36)]))))) (.cycle 0 [(.support 0 1 34 28), (.pair 1 2 192), (.pair 2 3 170), (.pair 3 4 192), (.support 4 0 28 34)])) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 226), (.pair 2 3 195), (.pair 3 4 170), (.support 4 0 37 36)]) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 227), (.pair 2 3 195), (.pair 3 4 195), (.support 4 0 37 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 227), (.support 2 3 39 39), (.pair 3 4 170), (.support 4 0 37 36)]))) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 192), (.pair 2 3 170), (.pair 3 4 170), (.support 4 0 37 36)])) (.cycle 0 [(.support 0 1 34 28), (.pair 1 2 192), (.pair 2 3 170), (.pair 3 4 170), (.support 4 0 37 34)]))))) (.split 2 (1083 / 640) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 192), (.pair 2 3 192), (.pair 3 4 170), (.support 4 0 28 36)]) (.split 3 (1083 / 640) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 170), (.pair 2 3 192), (.pair 3 4 192), (.support 4 0 28 36)]) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10881 / 6400) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 225), (.pair 2 3 195), (.pair 3 4 192), (.support 4 0 28 36)]) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 195), (.pair 2 3 195), (.pair 3 4 223), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 195), (.support 2 3 39 39), (.pair 3 4 192), (.support 4 0 28 36)]))) (.cycle 0 [(.support 0 1 36 39), (.pair 1 2 170), (.pair 2 3 170), (.pair 3 4 192), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 34 37), (.pair 1 2 170), (.pair 2 3 170), (.pair 3 4 192), (.support 4 0 28 34)])) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 170), (.pair 2 3 170), (.pair 3 4 170), (.support 4 0 37 36)])))))) (.split 0 (5517 / 3200) (.split 1 (1083 / 640) (.split 2 (1083 / 640) (.split 3 (1083 / 640) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 222), (.pair 2 3 222), (.pair 3 4 187), (.support 4 0 27 27)]) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 222), (.pair 2 3 192), (.support 3 4 37 27), (.support 4 0 27 27)])) (.split 3 (1083 / 640) (.split 4 (5517 / 3200) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 192), (.pair 2 3 192), (.pair 3 4 185), (.support 4 0 27 27)]) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 192), (.pair 2 3 192), (.support 3 4 28 36), (.support 4 0 36 27)])) (.split 4 (5517 / 3200) (.split 0 (10983 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 192), (.pair 2 3 170), (.support 3 4 37 27), (.support 4 0 27 27)]) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 192), (.pair 2 3 170), (.support 3 4 37 27), (.support 4 0 27 41)])) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 192), (.pair 2 3 170), (.support 3 4 37 36), (.support 4 0 36 27)])))) (.split 2 (1083 / 640) (.split 3 (1083 / 640) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 192), (.pair 2 3 222), (.pair 3 4 187), (.support 4 0 27 27)]) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 192), (.pair 2 3 192), (.support 3 4 37 27), (.support 4 0 27 27)])) (.split 3 (1083 / 640) (.split 4 (5517 / 3200) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 195), (.pair 2 3 192), (.pair 3 4 185), (.support 4 0 27 27)]) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 170), (.pair 2 3 192), (.pair 3 4 185), (.support 4 0 27 27)])) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 170), (.pair 2 3 192), (.pair 3 4 185), (.support 4 0 27 41)])) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 170), (.pair 2 3 192), (.support 3 4 28 36), (.support 4 0 36 27)])) (.split 4 (5517 / 3200) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 225), (.pair 2 3 195), (.support 3 4 37 27), (.support 4 0 27 27)]) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 195), (.pair 2 3 195), (.support 3 4 37 27), (.support 4 0 27 27)]) (.outer ![27, 37, 39, 39, 27]))) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 170), (.pair 2 3 170), (.support 3 4 37 27), (.support 4 0 27 27)])) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 170), (.pair 2 3 170), (.support 3 4 37 27), (.support 4 0 27 41)])) (.outer ![27, 37, 37, 37, 36]))))) (.split 1 (1083 / 640) (.split 2 (1083 / 640) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 222), (.pair 2 3 192), (.support 3 4 28 27), (.support 4 0 27 36)]) (.split 3 (1083 / 640) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 192), (.pair 2 3 192), (.pair 3 4 187), (.support 4 0 27 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 192), (.pair 2 3 170), (.support 3 4 37 27), (.support 4 0 27 36)]))) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 170), (.pair 2 3 170), (.support 3 4 28 27), (.support 4 0 27 36)])))) (.split 4 (2733 / 1600) (.split 0 (5517 / 3200) (.split 1 (1083 / 640) (.split 2 (1083 / 640) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (10779 / 6400) (.inner ![230, 231, 200, 185, 201]) (.split 3 (10983 / 6400) (.inner ![230, 228, 201, 201, 201]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 228), (.support 2 3 40 41), (.pair 3 4 185), (.pair 4 0 201)]))) (.split 2 (10779 / 6400) (.split 3 (10983 / 6400) (.inner ![201, 228, 230, 201, 201]) (.split 4 (10779 / 6400) (.inner ![201, 228, 200, 200, 230]) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 228), (.pair 2 3 200), (.support 3 4 41 40), (.pair 4 0 201)]))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.inner ![201, 222, 201, 230, 230]) .local) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 222), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 230)]) (.split 0 (4383 / 2560) (.cycle 0 [(.pair 0 1 273), (.pair 1 2 222), (.support 2 3 40 41), (.support 3 4 41 40), (.pair 4 0 273)]) (.split 1 (21609 / 12800) (.cycle 0 [(.pair 0 1 271), (.pair 1 2 245), (.support 2 3 40 41), (.support 3 4 41 40), (.pair 4 0 201)]) (.split 2 (21609 / 12800) (.split 3 (22017 / 12800) (.split 4 (21609 / 12800) (.inner ![201, 245, 262, 262, 271]) (.cycle 0 [(.support 0 1 47 45), (.pair 1 2 245), (.pair 2 3 262), (.support 3 4 41 45), (.support 4 0 45 47)])) (.cycle 0 [(.support 0 1 47 45), (.pair 1 2 245), (.support 2 3 40 46), (.support 3 4 46 40), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 47 45), (.pair 1 2 222), (.support 2 3 45 41), (.support 3 4 41 40), (.pair 4 0 201)])))))))) (.split 1 (10779 / 6400) (.split 2 (10779 / 6400) (.split 3 (10983 / 6400) (.inner ![200, 231, 230, 201, 185]) (.split 4 (10779 / 6400) (.inner ![200, 231, 200, 200, 200]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 231), (.pair 2 3 200), (.support 3 4 41 40), (.support 4 0 40 41)]))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.inner ![200, 228, 201, 230, 200]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 228), (.pair 2 3 201), (.pair 3 4 201), (.support 4 0 40 41)])) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 228), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 200)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 228), (.support 2 3 40 41), (.support 3 4 41 40), (.support 4 0 40 41)])))) (.split 2 (10779 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 228), (.pair 2 3 230), (.pair 3 4 201), (.pair 4 0 185)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 228), (.pair 2 3 200), (.pair 3 4 200), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 228), (.pair 2 3 200), (.support 3 4 41 40), (.support 4 0 40 41)]))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 222), (.pair 2 3 201), (.pair 3 4 230), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (21609 / 12800) (.inner ![262, 253, 271, 201, 265]) (.split 3 (4383 / 2560) (.inner ![262, 245, 273, 273, 265]) (.split 4 (21609 / 12800) (.inner ![262, 245, 201, 271, 262]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 245), (.support 2 3 45 47), (.support 3 4 47 45), (.support 4 0 45 41)])))) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 222), (.pair 2 3 201), (.pair 3 4 201), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 222), (.pair 2 3 201), (.pair 3 4 201), (.support 4 0 40 46)]))) (.split 4 (10779 / 6400) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 245), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 270)]) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 222), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 270)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 222), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 200)])) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (21609 / 12800) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 253), (.support 2 3 40 41), (.support 3 4 41 40), (.support 4 0 40 41)]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 245), (.support 2 3 45 41), (.support 3 4 41 40), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 222), (.support 2 3 40 41), (.support 3 4 41 40), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 222), (.support 2 3 40 41), (.support 3 4 41 40), (.support 4 0 40 46)]))))))) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 228), (.pair 2 3 185), (.support 3 4 27 37), (.support 4 0 37 27)]) (.split 2 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 228), (.pair 2 3 200), (.support 3 4 27 37), (.support 4 0 37 27)]) (.split 3 (10983 / 6400) .local (.cycle 0 [(.pair 0 1 201), (.pair 1 2 222), (.support 2 3 40 41), (.support 3 4 41 37), (.support 4 0 37 27)])))) (.split 1 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 228), (.pair 2 3 185), (.support 3 4 27 37), (.support 4 0 37 41)]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 222), (.pair 2 3 185), (.support 3 4 27 37), (.support 4 0 37 41)])))) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 228), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 201)]) (.split 2 (10779 / 6400) (.split 3 (2217 / 1280) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 228), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 230)]) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 228), (.support 2 3 28 36), (.support 3 4 36 40), (.pair 4 0 201)])) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 228), (.support 2 3 28 34), (.support 3 4 34 28), (.pair 4 0 201)])) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 222), (.support 2 3 40 36), (.support 3 4 36 28), (.pair 4 0 201)]))) (.split 1 (10779 / 6400) (.split 2 (10779 / 6400) (.split 3 (2217 / 1280) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 231), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 200)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 231), (.support 2 3 28 36), (.support 3 4 36 40), (.support 4 0 40 41)])) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 231), (.support 2 3 28 34), (.support 3 4 34 28), (.pair 4 0 185)])) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 228), (.support 2 3 40 36), (.support 3 4 36 28), (.pair 4 0 185)])) (.split 2 (10779 / 6400) (.split 3 (2217 / 1280) (.split 4 (10779 / 6400) (.split 0 (22017 / 12800) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 228), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 270)]) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 228), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 200)])) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 228), (.support 2 3 28 36), (.support 3 4 36 40), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 228), (.support 2 3 28 34), (.support 3 4 34 28), (.pair 4 0 185)])) (.split 3 (2217 / 1280) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 222), (.support 2 3 40 36), (.support 3 4 36 28), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 222), (.support 2 3 40 36), (.support 3 4 36 40), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 222), (.support 2 3 40 34), (.support 3 4 34 28), (.pair 4 0 185)]))))) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 222), (.support 2 3 28 36), (.support 3 4 36 37), (.support 4 0 37 27)]))) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 226), (.support 2 3 37 27), (.pair 3 4 201), (.pair 4 0 201)]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 226), (.support 2 3 37 41), (.pair 3 4 185), (.pair 4 0 201)])) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 227), (.support 2 3 39 27), (.pair 3 4 185), (.pair 4 0 201)])) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 223), (.support 2 3 37 27), (.pair 3 4 230), (.pair 4 0 230)]) .local) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 223), (.support 2 3 37 41), (.pair 3 4 200), (.pair 4 0 230)]) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 223), (.support 2 3 37 41), (.support 3 4 41 40), (.pair 4 0 201)]))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 192), (.support 2 3 39 27), (.pair 3 4 230), (.pair 4 0 230)]) .local) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 192), (.support 2 3 39 41), (.pair 3 4 185), (.pair 4 0 201)])))) (.split 1 (10779 / 6400) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 226), (.support 2 3 37 27), (.pair 3 4 230), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21507 / 12800) (.cycle 0 [(.pair 0 1 293), (.pair 1 2 257), (.support 2 3 37 27), (.pair 3 4 201), (.support 4 0 40 41)]) (.split 2 (21711 / 12800) (.cycle 0 [(.pair 0 1 270), (.pair 1 2 259), (.support 2 3 37 27), (.pair 3 4 201), (.support 4 0 40 41)]) (.cycle 0 [(.pair 0 1 270), (.pair 1 2 226), (.support 2 3 44 27), (.pair 3 4 201), (.support 4 0 40 41)]))) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 226), (.support 2 3 37 27), (.pair 3 4 201), (.support 4 0 40 46)]))) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 226), (.support 2 3 37 41), (.pair 3 4 200), (.pair 4 0 200)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 226), (.support 2 3 37 41), (.support 3 4 41 40), (.support 4 0 40 41)]))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 227), (.support 2 3 39 27), (.pair 3 4 230), (.pair 4 0 200)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 227), (.support 2 3 39 27), (.pair 3 4 201), (.support 4 0 40 41)])) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 227), (.support 2 3 39 41), (.pair 3 4 185), (.pair 4 0 185)]))) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 250), (.support 2 3 37 27), (.pair 3 4 230), (.pair 4 0 270)]) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 223), (.support 2 3 37 27), (.pair 3 4 230), (.pair 4 0 270)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 223), (.support 2 3 37 27), (.pair 3 4 230), (.pair 4 0 200)])) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (21711 / 12800) (.split 3 (4383 / 2560) (.split 4 (21609 / 12800) (.inner ![262, 243, 278, 272, 262]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 243), (.support 2 3 37 27), (.pair 3 4 273), (.support 4 0 45 41)])) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 243), (.support 2 3 37 47), (.pair 3 4 201), (.support 4 0 40 41)])) (.split 3 (4383 / 2560) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 250), (.support 2 3 44 27), (.pair 3 4 273), (.support 4 0 40 41)]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 250), (.support 2 3 44 47), (.pair 3 4 201), (.support 4 0 40 41)]))) (.split 2 (21711 / 12800) (.split 3 (4383 / 2560) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 248), (.support 2 3 37 27), (.pair 3 4 273), (.support 4 0 40 41)]) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 248), (.support 2 3 37 47), (.pair 3 4 201), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 223), (.support 2 3 44 27), (.pair 3 4 201), (.support 4 0 40 41)]))) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 223), (.support 2 3 37 27), (.pair 3 4 201), (.support 4 0 40 46)]))) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 223), (.support 2 3 37 41), (.pair 3 4 200), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 223), (.support 2 3 37 41), (.support 3 4 41 40), (.support 4 0 40 41)]))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 192), (.support 2 3 39 27), (.pair 3 4 230), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (21813 / 12800) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 251), (.support 2 3 39 27), (.pair 3 4 201), (.support 4 0 40 41)]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 244), (.support 2 3 43 27), (.pair 3 4 201), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 192), (.support 2 3 39 27), (.pair 3 4 201), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 192), (.support 2 3 39 27), (.pair 3 4 201), (.support 4 0 40 46)]))) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 192), (.support 2 3 39 41), (.pair 3 4 200), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 192), (.support 2 3 39 41), (.support 3 4 41 40), (.support 4 0 40 41)])))))) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (10881 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 226), (.support 2 3 37 27), (.support 3 4 27 37), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 227), (.support 2 3 39 27), (.support 3 4 27 37), (.support 4 0 37 27)])) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) .local (.cycle 0 [(.pair 0 1 201), (.pair 1 2 223), (.support 2 3 37 41), (.support 3 4 41 37), (.support 4 0 37 27)])) (.split 3 (10983 / 6400) .local (.cycle 0 [(.pair 0 1 201), (.pair 1 2 192), (.support 2 3 39 41), (.support 3 4 41 37), (.support 4 0 37 27)])))) (.split 1 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 227), (.support 2 3 37 27), (.support 3 4 27 37), (.support 4 0 37 41)]) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 223), (.support 2 3 37 27), (.support 3 4 27 37), (.support 4 0 37 41)]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 192), (.support 2 3 39 27), (.support 3 4 27 37), (.support 4 0 37 41)]))))) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 192), (.support 2 3 37 36), (.support 3 4 36 28), (.pair 4 0 201)]) (.split 1 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 227), (.support 2 3 37 36), (.support 3 4 36 28), (.pair 4 0 185)]) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 223), (.support 2 3 37 36), (.support 3 4 36 28), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 192), (.support 2 3 39 36), (.support 3 4 36 28), (.pair 4 0 185)])))) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 192), (.support 2 3 37 36), (.support 3 4 36 37), (.support 4 0 37 27)])))) (.split 2 (1083 / 640) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10779 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 226), (.pair 2 3 230), (.pair 3 4 201), (.pair 4 0 201)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 226), (.pair 2 3 200), (.pair 3 4 200), (.pair 4 0 230)]) (.split 0 (4383 / 2560) (.split 1 (21711 / 12800) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 259), (.pair 2 3 200), (.support 3 4 41 40), (.pair 4 0 273)]) (.cycle 0 [(.support 0 1 27 44), (.pair 1 2 226), (.pair 2 3 200), (.support 3 4 41 40), (.pair 4 0 273)])) (.cycle 0 [(.support 0 1 47 37), (.pair 1 2 226), (.pair 2 3 200), (.support 3 4 41 40), (.pair 4 0 201)])))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 223), (.pair 2 3 201), (.pair 3 4 230), (.pair 4 0 230)]) .local) (.split 4 (10779 / 6400) (.split 0 (4383 / 2560) (.split 1 (21711 / 12800) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 248), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 277)]) (.cycle 0 [(.support 0 1 27 44), (.pair 1 2 223), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 277)])) (.cycle 0 [(.support 0 1 47 37), (.pair 1 2 223), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 230)])) (.split 0 (4383 / 2560) (.split 1 (21711 / 12800) (.split 2 (21609 / 12800) (.split 3 (22017 / 12800) (.split 4 (21609 / 12800) (.inner ![278, 243, 262, 262, 272]) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 243), (.pair 2 3 262), (.support 3 4 41 45), (.pair 4 0 273)])) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 243), (.support 2 3 40 46), (.support 3 4 46 40), (.pair 4 0 273)])) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 248), (.support 2 3 45 41), (.support 3 4 41 40), (.pair 4 0 273)])) (.split 2 (21609 / 12800) (.cycle 0 [(.support 0 1 27 44), (.pair 1 2 250), (.support 2 3 40 41), (.support 3 4 41 40), (.pair 4 0 273)]) (.cycle 0 [(.support 0 1 27 44), (.pair 1 2 223), (.support 2 3 45 41), (.support 3 4 41 40), (.pair 4 0 273)]))) (.split 1 (21711 / 12800) (.split 2 (21609 / 12800) (.cycle 0 [(.support 0 1 47 37), (.pair 1 2 243), (.support 2 3 40 41), (.support 3 4 41 40), (.pair 4 0 201)]) (.cycle 0 [(.support 0 1 47 37), (.pair 1 2 248), (.support 2 3 45 41), (.support 3 4 41 40), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 47 44), (.pair 1 2 223), (.support 2 3 40 41), (.support 3 4 41 40), (.pair 4 0 201)])))))) (.split 2 (10779 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 227), (.pair 2 3 230), (.pair 3 4 201), (.pair 4 0 201)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 227), (.pair 2 3 200), (.pair 3 4 200), (.pair 4 0 230)]) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 227), (.pair 2 3 200), (.support 3 4 41 40), (.pair 4 0 201)]))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 192), (.pair 2 3 201), (.pair 3 4 230), (.pair 4 0 230)]) .local) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 192), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 230)]) (.split 0 (4383 / 2560) (.split 1 (21813 / 12800) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 240), (.support 2 3 40 41), (.support 3 4 41 40), (.pair 4 0 273)]) (.cycle 0 [(.support 0 1 27 43), (.pair 1 2 192), (.support 2 3 40 41), (.support 3 4 41 40), (.pair 4 0 273)])) (.cycle 0 [(.support 0 1 47 39), (.pair 1 2 192), (.support 2 3 40 41), (.support 3 4 41 40), (.pair 4 0 201)])))))) (.split 1 (10881 / 6400) (.split 2 (10779 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 226), (.pair 2 3 230), (.pair 3 4 201), (.pair 4 0 185)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 226), (.pair 2 3 200), (.pair 3 4 200), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 226), (.pair 2 3 200), (.support 3 4 41 40), (.support 4 0 40 41)]))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 223), (.pair 2 3 201), (.pair 3 4 230), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 223), (.pair 2 3 201), (.pair 3 4 201), (.support 4 0 40 41)])) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 223), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 223), (.support 2 3 40 41), (.support 3 4 41 40), (.support 4 0 40 41)])))) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 41 39), (.pair 1 2 227), (.pair 2 3 200), (.pair 3 4 185), (.pair 4 0 185)]) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 41 39), (.pair 1 2 192), (.pair 2 3 201), (.pair 3 4 201), (.pair 4 0 185)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 39), (.pair 1 2 192), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 39), (.pair 1 2 192), (.support 2 3 40 41), (.support 3 4 41 40), (.support 4 0 40 41)])))))) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10779 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 226), (.pair 2 3 230), (.support 3 4 27 37), (.support 4 0 37 27)]) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 226), (.pair 2 3 200), (.support 3 4 41 37), (.support 4 0 37 27)])) (.split 3 (10983 / 6400) .local (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 223), (.support 2 3 40 41), (.support 3 4 41 37), (.support 4 0 37 27)]))) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 227), (.pair 2 3 200), (.support 3 4 27 37), (.support 4 0 37 27)]) (.split 3 (10983 / 6400) .local (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 192), (.support 2 3 40 41), (.support 3 4 41 37), (.support 4 0 37 27)])))) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 192), (.pair 2 3 185), (.support 3 4 27 37), (.support 4 0 37 41)]))) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10779 / 6400) (.split 3 (2217 / 1280) (.split 4 (10779 / 6400) (.split 0 (4383 / 2560) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 226), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 277)]) (.cycle 0 [(.support 0 1 47 37), (.pair 1 2 226), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 230)])) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 226), (.support 2 3 28 36), (.support 3 4 36 40), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 226), (.support 2 3 28 34), (.support 3 4 34 28), (.pair 4 0 201)])) (.split 3 (2217 / 1280) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 223), (.support 2 3 40 36), (.support 3 4 36 28), (.pair 4 0 230)]) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 223), (.support 2 3 40 36), (.support 3 4 36 40), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 223), (.support 2 3 40 34), (.support 3 4 34 28), (.pair 4 0 201)]))) (.split 2 (10779 / 6400) (.split 3 (2217 / 1280) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 227), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 230)]) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 227), (.support 2 3 28 36), (.support 3 4 36 40), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 227), (.support 2 3 28 34), (.support 3 4 34 28), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 192), (.support 2 3 40 36), (.support 3 4 36 28), (.pair 4 0 201)]))) (.split 1 (10881 / 6400) (.split 2 (10779 / 6400) (.split 3 (2217 / 1280) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 226), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 226), (.support 2 3 28 36), (.support 3 4 36 40), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 226), (.support 2 3 28 34), (.support 3 4 34 28), (.pair 4 0 185)])) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 223), (.support 2 3 40 36), (.support 3 4 36 28), (.pair 4 0 185)])) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 41 39), (.pair 1 2 227), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 41 39), (.pair 1 2 192), (.support 2 3 40 36), (.support 3 4 36 28), (.pair 4 0 185)])))) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 192), (.support 2 3 28 36), (.support 3 4 36 37), (.support 4 0 37 27)]))) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.split 0 (4383 / 2560) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 225), (.support 2 3 37 27), (.pair 3 4 230), (.pair 4 0 277)]) (.cycle 0 [(.support 0 1 47 37), (.pair 1 2 225), (.support 2 3 37 27), (.pair 3 4 230), (.pair 4 0 230)])) .local) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 225), (.support 2 3 37 41), (.pair 3 4 200), (.pair 4 0 230)]) (.split 0 (4383 / 2560) (.split 1 (21711 / 12800) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 283), (.support 2 3 37 41), (.support 3 4 41 40), (.pair 4 0 273)]) (.cycle 0 [(.support 0 1 27 44), (.pair 1 2 225), (.support 2 3 37 41), (.support 3 4 41 40), (.pair 4 0 273)])) (.cycle 0 [(.support 0 1 47 37), (.pair 1 2 225), (.support 2 3 37 41), (.support 3 4 41 40), (.pair 4 0 201)])))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 195), (.support 2 3 39 27), (.pair 3 4 230), (.pair 4 0 230)]) .local) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 195), (.support 2 3 39 41), (.pair 3 4 200), (.pair 4 0 230)]) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 195), (.support 2 3 39 41), (.support 3 4 41 40), (.pair 4 0 201)])))) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 195), (.support 2 3 37 27), (.pair 3 4 230), (.pair 4 0 230)]) .local) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 195), (.support 2 3 37 41), (.pair 3 4 200), (.pair 4 0 230)]) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 195), (.support 2 3 37 41), (.support 3 4 41 40), (.pair 4 0 201)]))) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 27 39), (.support 1 2 39 39), (.support 2 3 39 27), (.pair 3 4 201), (.pair 4 0 201)]) (.cycle 0 [(.support 0 1 27 39), (.support 1 2 39 39), (.support 2 3 39 41), (.pair 3 4 185), (.pair 4 0 201)])))) (.split 1 (10881 / 6400) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 225), (.support 2 3 37 27), (.pair 3 4 230), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21711 / 12800) (.split 2 (21711 / 12800) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 284), (.support 2 3 37 27), (.pair 3 4 201), (.support 4 0 40 41)]) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 283), (.support 2 3 44 27), (.pair 3 4 201), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 44), (.pair 1 2 225), (.support 2 3 37 27), (.pair 3 4 201), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 46 37), (.pair 1 2 225), (.support 2 3 37 27), (.pair 3 4 201), (.support 4 0 40 46)]))) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 225), (.support 2 3 37 41), (.pair 3 4 200), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 225), (.support 2 3 37 41), (.support 3 4 41 40), (.support 4 0 40 41)]))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 195), (.support 2 3 39 27), (.pair 3 4 230), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 195), (.support 2 3 39 27), (.pair 3 4 201), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 195), (.support 2 3 39 41), (.pair 3 4 185), (.pair 4 0 185)]))) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 39), (.pair 1 2 195), (.support 2 3 37 27), (.pair 3 4 230), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 39), (.pair 1 2 195), (.support 2 3 37 27), (.pair 3 4 201), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 39), (.pair 1 2 195), (.support 2 3 37 41), (.pair 3 4 185), (.pair 4 0 185)])) (.cycle 0 [(.support 0 1 41 39), (.support 1 2 39 39), (.support 2 3 39 27), (.pair 3 4 185), (.pair 4 0 185)])))) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) .local (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 225), (.support 2 3 37 41), (.support 3 4 41 37), (.support 4 0 37 27)])) (.split 3 (10983 / 6400) .local (.outer ![27, 37, 39, 41, 37]))) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) .local (.outer ![27, 39, 37, 41, 37])) (.outer ![27, 39, 39, 27, 37]))) (.split 1 (10881 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 195), (.support 2 3 37 27), (.support 3 4 27 37), (.support 4 0 37 41)]) (.outer ![41, 39, 37, 27, 37])))) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 225), (.support 2 3 37 36), (.support 3 4 36 28), (.pair 4 0 201)]) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 195), (.support 2 3 39 36), (.support 3 4 36 28), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 27 39), (.pair 1 2 170), (.support 2 3 37 36), (.support 3 4 36 28), (.pair 4 0 201)])) (.split 1 (10881 / 6400) (.cycle 0 [(.support 0 1 41 37), (.pair 1 2 195), (.support 2 3 37 36), (.support 3 4 36 28), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 41 39), (.pair 1 2 170), (.support 2 3 37 36), (.support 3 4 36 28), (.pair 4 0 185)]))) (.outer ![27, 37, 37, 36, 37]))))) (.split 1 (1083 / 640) (.split 2 (1083 / 640) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (10779 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 231), (.pair 2 3 230), (.pair 3 4 201), (.support 4 0 28 36)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 231), (.pair 2 3 200), (.pair 3 4 200), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 231), (.pair 2 3 200), (.support 3 4 41 40), (.support 4 0 40 36)]))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 228), (.pair 2 3 201), (.pair 3 4 230), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 228), (.pair 2 3 201), (.pair 3 4 201), (.support 4 0 40 36)])) (.split 4 (10779 / 6400) (.split 0 (22119 / 12800) (.split 1 (21507 / 12800) (.cycle 0 [(.pair 0 1 287), (.pair 1 2 236), (.support 2 3 40 41), (.pair 3 4 200), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 42), (.pair 1 2 228), (.support 2 3 40 41), (.pair 3 4 200), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 48 28), (.pair 1 2 228), (.support 2 3 40 41), (.pair 3 4 200), (.support 4 0 28 48)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 228), (.support 2 3 40 41), (.support 3 4 41 40), (.support 4 0 40 36)])))) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 228), (.pair 2 3 200), (.pair 3 4 185), (.support 4 0 28 36)]) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 222), (.pair 2 3 201), (.pair 3 4 201), (.support 4 0 28 36)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 222), (.support 2 3 40 41), (.pair 3 4 200), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 222), (.support 2 3 40 41), (.support 3 4 41 40), (.support 4 0 40 36)]))))) (.cycle 0 [(.support 0 1 34 28), (.pair 1 2 222), (.pair 2 3 185), (.pair 3 4 185), (.support 4 0 28 34)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 222), (.pair 2 3 185), (.support 3 4 27 37), (.support 4 0 37 36)])) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (10779 / 6400) (.split 3 (2217 / 1280) (.split 4 (10779 / 6400) (.split 0 (22119 / 12800) (.split 1 (21507 / 12800) (.cycle 0 [(.pair 0 1 287), (.pair 1 2 255), (.support 2 3 28 36), (.support 3 4 36 28), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 42), (.pair 1 2 231), (.support 2 3 28 36), (.support 3 4 36 28), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 48 28), (.pair 1 2 231), (.support 2 3 28 36), (.support 3 4 36 28), (.support 4 0 28 48)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 231), (.support 2 3 28 36), (.support 3 4 36 40), (.support 4 0 40 36)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 231), (.support 2 3 28 34), (.support 3 4 34 28), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 228), (.support 2 3 40 36), (.support 3 4 36 28), (.support 4 0 28 36)])) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 228), (.support 2 3 28 36), (.support 3 4 36 28), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 222), (.support 2 3 40 36), (.support 3 4 36 28), (.support 4 0 28 36)]))) (.cycle 0 [(.support 0 1 34 28), (.pair 1 2 222), (.support 2 3 28 36), (.support 3 4 36 28), (.support 4 0 28 34)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 222), (.support 2 3 28 36), (.support 3 4 36 37), (.support 4 0 37 36)]))) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.split 0 (22119 / 12800) (.split 1 (21507 / 12800) (.cycle 0 [(.pair 0 1 287), (.pair 1 2 257), (.support 2 3 37 27), (.pair 3 4 230), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 42), (.pair 1 2 226), (.support 2 3 37 27), (.pair 3 4 230), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 48 28), (.pair 1 2 226), (.support 2 3 37 27), (.pair 3 4 230), (.support 4 0 28 48)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 226), (.support 2 3 37 27), (.pair 3 4 201), (.support 4 0 40 36)])) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 226), (.support 2 3 37 41), (.pair 3 4 200), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 226), (.support 2 3 37 41), (.support 3 4 41 40), (.support 4 0 40 36)]))) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 227), (.support 2 3 39 27), (.pair 3 4 230), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 227), (.support 2 3 39 27), (.pair 3 4 201), (.support 4 0 40 36)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 227), (.support 2 3 39 41), (.pair 3 4 185), (.support 4 0 28 36)]))) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 223), (.support 2 3 37 27), (.pair 3 4 230), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 223), (.support 2 3 37 27), (.pair 3 4 201), (.support 4 0 40 36)])) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 223), (.support 2 3 37 41), (.pair 3 4 185), (.support 4 0 28 36)])) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 192), (.support 2 3 39 27), (.pair 3 4 201), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 192), (.support 2 3 39 41), (.pair 3 4 185), (.support 4 0 28 36)])))) (.split 1 (10779 / 6400) (.cycle 0 [(.support 0 1 34 28), (.pair 1 2 227), (.support 2 3 37 27), (.pair 3 4 185), (.support 4 0 28 34)]) (.cycle 0 [(.support 0 1 34 40), (.pair 1 2 192), (.support 2 3 37 27), (.pair 3 4 185), (.support 4 0 28 34)]))) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 192), (.support 2 3 37 27), (.support 3 4 27 37), (.support 4 0 37 36)])) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 227), (.support 2 3 37 36), (.support 3 4 36 28), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 192), (.support 2 3 37 36), (.support 3 4 36 28), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 34 28), (.pair 1 2 192), (.support 2 3 37 36), (.support 3 4 36 28), (.support 4 0 28 34)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 192), (.support 2 3 37 36), (.support 3 4 36 37), (.support 4 0 37 36)])))) (.split 2 (1083 / 640) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10881 / 6400) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 226), (.pair 2 3 200), (.pair 3 4 185), (.support 4 0 28 36)]) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 223), (.pair 2 3 201), (.pair 3 4 201), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 223), (.support 2 3 40 41), (.pair 3 4 185), (.support 4 0 28 36)]))) (.cycle 0 [(.support 0 1 36 39), (.pair 1 2 192), (.pair 2 3 185), (.pair 3 4 185), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 34 37), (.pair 1 2 192), (.pair 2 3 185), (.pair 3 4 185), (.support 4 0 28 34)])) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 192), (.pair 2 3 185), (.support 3 4 27 37), (.support 4 0 37 36)])) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10881 / 6400) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 223), (.support 2 3 28 36), (.support 3 4 36 28), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 39), (.pair 1 2 192), (.support 2 3 28 36), (.support 3 4 36 28), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 34 37), (.pair 1 2 192), (.support 2 3 28 36), (.support 3 4 36 28), (.support 4 0 28 34)])) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 192), (.support 2 3 28 36), (.support 3 4 36 37), (.support 4 0 37 36)]))) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10881 / 6400) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 225), (.support 2 3 37 27), (.pair 3 4 201), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 225), (.support 2 3 37 41), (.pair 3 4 185), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 195), (.support 2 3 39 27), (.pair 3 4 185), (.support 4 0 28 36)])) (.split 2 (10881 / 6400) (.cycle 0 [(.support 0 1 36 39), (.pair 1 2 195), (.support 2 3 37 27), (.pair 3 4 185), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 39), (.support 1 2 39 39), (.support 2 3 39 27), (.pair 3 4 185), (.support 4 0 28 36)]))) (.cycle 0 [(.support 0 1 34 37), (.pair 1 2 170), (.support 2 3 37 27), (.pair 3 4 185), (.support 4 0 28 34)])) (.outer ![36, 37, 37, 27, 37])) (.cycle 0 [(.support 0 1 36 37), (.pair 1 2 170), (.support 2 3 37 36), (.support 3 4 36 28), (.support 4 0 28 36)]))))) (.split 0 (5517 / 3200) (.split 1 (1083 / 640) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 192), (.support 2 3 28 27), (.support 3 4 27 27), (.support 4 0 27 27)]) (.split 2 (1083 / 640) (.cycle 0 [(.support 0 1 27 37), (.pair 1 2 192), (.pair 2 3 187), (.support 3 4 27 27), (.support 4 0 27 27)]) (.outer ![27, 37, 37, 27, 27]))) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 170), (.support 2 3 28 27), (.support 3 4 27 27), (.support 4 0 27 36)])))) (.split 3 (2733 / 1600) (.split 4 (2733 / 1600) (.split 0 (5517 / 3200) (.split 1 (1083 / 640) (.split 2 (5517 / 3200) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.inner ![230, 230, 201, 222, 201]) (.split 3 (10779 / 6400) (.inner ![230, 200, 200, 228, 201]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 222), (.pair 4 0 201)]))) (.split 2 (10983 / 6400) (.split 3 (10779 / 6400) (.inner ![201, 201, 230, 228, 201]) (.split 4 (10779 / 6400) (.inner ![201, 201, 201, 228, 230]) .local)) (.split 3 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.pair 2 3 200), (.pair 3 4 228), (.pair 4 0 201)]) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.support 2 3 41 40), (.pair 3 4 228), (.pair 4 0 230)]) (.split 0 (4383 / 2560) (.cycle 0 [(.pair 0 1 273), (.support 1 2 40 41), (.support 2 3 41 40), (.pair 3 4 222), (.pair 4 0 273)]) (.split 1 (21609 / 12800) (.split 2 (22017 / 12800) (.split 3 (21609 / 12800) (.inner ![271, 262, 262, 245, 201]) (.cycle 0 [(.pair 0 1 271), (.pair 1 2 262), (.support 2 3 41 45), (.pair 3 4 222), (.pair 4 0 201)])) (.cycle 0 [(.pair 0 1 271), (.support 1 2 40 46), (.support 2 3 46 40), (.pair 3 4 222), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 47 45), (.support 1 2 45 41), (.support 2 3 41 40), (.pair 3 4 222), (.pair 4 0 201)]))))))) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.split 3 (10779 / 6400) (.inner ![200, 230, 230, 228, 185]) (.split 4 (10779 / 6400) (.inner ![200, 230, 201, 228, 200]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 230), (.pair 2 3 201), (.pair 3 4 222), (.support 4 0 40 41)]))) (.split 3 (10779 / 6400) (.split 4 (10779 / 6400) (.inner ![200, 200, 200, 231, 200]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.pair 2 3 200), (.pair 3 4 228), (.support 4 0 40 41)])) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 228), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21507 / 12800) (.cycle 0 [(.pair 0 1 293), (.pair 1 2 237), (.support 2 3 41 40), (.pair 3 4 222), (.support 4 0 40 41)]) (.split 2 (22017 / 12800) (.cycle 0 [(.pair 0 1 270), (.pair 1 2 270), (.support 2 3 41 40), (.pair 3 4 222), (.support 4 0 40 41)]) (.cycle 0 [(.pair 0 1 270), (.pair 1 2 200), (.support 2 3 46 40), (.pair 3 4 222), (.support 4 0 40 41)]))) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 222), (.support 4 0 40 46)]))))) (.split 2 (10983 / 6400) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.pair 2 3 230), (.pair 3 4 228), (.pair 4 0 185)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.pair 2 3 201), (.pair 3 4 228), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (4383 / 2560) (.inner ![262, 272, 273, 222, 265]) (.split 3 (21609 / 12800) (.inner ![262, 271, 271, 245, 265]) (.split 4 (21609 / 12800) (.inner ![262, 271, 201, 245, 262]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 271), (.support 2 3 47 45), (.pair 3 4 222), (.support 4 0 45 41)])))) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 201), (.pair 2 3 201), (.pair 3 4 222), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 201), (.pair 2 3 201), (.pair 3 4 222), (.support 4 0 40 46)])))) (.split 3 (10779 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.pair 2 3 200), (.pair 3 4 231), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.pair 2 3 200), (.pair 3 4 228), (.support 4 0 40 41)])) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.support 2 3 41 40), (.pair 3 4 228), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (22017 / 12800) (.split 3 (21609 / 12800) (.split 4 (21609 / 12800) (.inner ![262, 262, 262, 253, 262]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 262), (.pair 2 3 262), (.pair 3 4 245), (.support 4 0 45 41)])) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 262), (.support 2 3 41 45), (.pair 3 4 222), (.support 4 0 40 41)])) (.cycle 0 [(.pair 0 1 262), (.support 1 2 40 46), (.support 2 3 46 40), (.pair 3 4 222), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 45), (.support 1 2 45 41), (.support 2 3 41 40), (.pair 3 4 222), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 46 40), (.support 1 2 40 41), (.support 2 3 41 40), (.pair 3 4 222), (.support 4 0 40 46)]))))))) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.split 3 (10779 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 230), (.pair 2 3 230), (.pair 3 4 227), (.support 4 0 37 27)]) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 230), (.pair 2 3 201), (.pair 3 4 223), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 230), (.pair 2 3 201), (.pair 3 4 192), (.support 4 0 39 27)]))) (.split 3 (10779 / 6400) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.pair 2 3 200), (.pair 3 4 226), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.pair 2 3 200), (.pair 3 4 227), (.support 4 0 39 27)])) (.split 4 (10881 / 6400) (.split 0 (4383 / 2560) (.split 1 (21507 / 12800) (.cycle 0 [(.pair 0 1 302), (.pair 1 2 237), (.support 2 3 41 40), (.pair 3 4 223), (.support 4 0 37 27)]) (.split 2 (22017 / 12800) (.cycle 0 [(.pair 0 1 277), (.pair 1 2 270), (.support 2 3 41 40), (.pair 3 4 223), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 277), (.pair 1 2 200), (.support 2 3 46 40), (.pair 3 4 223), (.support 4 0 37 27)]))) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 223), (.support 4 0 37 47)])) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 192), (.support 4 0 39 27)])))) (.split 2 (10983 / 6400) (.split 3 (10779 / 6400) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 201), (.pair 2 3 230), (.pair 3 4 226), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 201), (.pair 2 3 230), (.pair 3 4 227), (.support 4 0 39 27)])) .local) (.split 3 (10779 / 6400) (.split 4 (10881 / 6400) (.split 0 (4383 / 2560) (.split 1 (21609 / 12800) (.cycle 0 [(.pair 0 1 272), (.support 1 2 40 41), (.pair 2 3 200), (.pair 3 4 226), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 273), (.support 1 2 45 41), (.pair 2 3 200), (.pair 3 4 226), (.support 4 0 37 27)])) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.pair 2 3 200), (.pair 3 4 226), (.support 4 0 37 47)])) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.pair 2 3 200), (.pair 3 4 227), (.support 4 0 39 27)])) (.split 4 (10881 / 6400) (.split 0 (4383 / 2560) (.split 1 (21609 / 12800) (.split 2 (22017 / 12800) (.split 3 (21609 / 12800) (.split 4 (21711 / 12800) (.inner ![272, 262, 262, 243, 278]) (.cycle 0 [(.pair 0 1 272), (.pair 1 2 262), (.pair 2 3 262), (.pair 3 4 250), (.support 4 0 44 27)])) (.cycle 0 [(.pair 0 1 272), (.pair 1 2 262), (.support 2 3 41 45), (.pair 3 4 223), (.support 4 0 37 27)])) (.cycle 0 [(.pair 0 1 272), (.support 1 2 40 46), (.support 2 3 46 40), (.pair 3 4 223), (.support 4 0 37 27)])) (.split 2 (22017 / 12800) (.split 3 (21609 / 12800) (.cycle 0 [(.pair 0 1 273), (.support 1 2 45 41), (.pair 2 3 262), (.pair 3 4 250), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 273), (.support 1 2 45 41), (.support 2 3 41 45), (.pair 3 4 223), (.support 4 0 37 27)])) (.cycle 0 [(.pair 0 1 273), (.support 1 2 45 46), (.support 2 3 46 40), (.pair 3 4 223), (.support 4 0 37 27)]))) (.split 1 (21609 / 12800) (.split 2 (22017 / 12800) (.split 3 (21609 / 12800) (.cycle 0 [(.pair 0 1 271), (.pair 1 2 262), (.pair 2 3 262), (.pair 3 4 250), (.support 4 0 37 47)]) (.cycle 0 [(.pair 0 1 271), (.pair 1 2 262), (.support 2 3 41 45), (.pair 3 4 223), (.support 4 0 37 47)])) (.cycle 0 [(.pair 0 1 271), (.support 1 2 40 46), (.support 2 3 46 40), (.pair 3 4 223), (.support 4 0 37 47)])) (.cycle 0 [(.support 0 1 47 45), (.support 1 2 45 41), (.support 2 3 41 40), (.pair 3 4 223), (.support 4 0 37 47)]))) (.split 0 (4383 / 2560) (.split 1 (21609 / 12800) (.cycle 0 [(.pair 0 1 272), (.support 1 2 40 41), (.support 2 3 41 40), (.pair 3 4 192), (.support 4 0 39 27)]) (.cycle 0 [(.pair 0 1 273), (.support 1 2 45 41), (.support 2 3 41 40), (.pair 3 4 192), (.support 4 0 39 27)])) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.support 2 3 41 40), (.pair 3 4 192), (.support 4 0 39 47)])))))) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 230), (.pair 2 3 201), (.pair 3 4 192), (.support 4 0 37 41)]) (.split 3 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.pair 2 3 200), (.pair 3 4 227), (.support 4 0 37 41)]) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 223), (.support 4 0 37 41)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 192), (.support 4 0 39 41)])))) (.split 2 (10983 / 6400) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.pair 2 3 230), (.pair 3 4 227), (.support 4 0 37 41)]) (.split 4 (10881 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.pair 2 3 201), (.pair 3 4 223), (.support 4 0 37 41)]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.pair 2 3 201), (.pair 3 4 192), (.support 4 0 39 41)]))) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.pair 2 3 200), (.pair 3 4 227), (.support 4 0 37 41)]) (.split 4 (10881 / 6400) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.support 2 3 41 40), (.pair 3 4 223), (.support 4 0 37 41)]) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.support 2 3 41 40), (.pair 3 4 192), (.support 4 0 39 41)]))))))) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 230), (.support 2 3 27 37), (.pair 3 4 223), (.pair 4 0 201)]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 230), (.support 2 3 27 39), (.pair 3 4 192), (.pair 4 0 201)])) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.support 2 3 41 37), (.pair 3 4 192), (.pair 4 0 201)])) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 201), (.support 2 3 27 37), (.pair 3 4 226), (.pair 4 0 230)]) .local) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 201), (.support 2 3 27 39), (.pair 3 4 227), (.pair 4 0 230)]) .local)) (.split 3 (10881 / 6400) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.support 2 3 41 37), (.pair 3 4 223), (.pair 4 0 201)]) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.support 2 3 41 39), (.pair 3 4 192), (.pair 4 0 201)])))) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 230), (.support 2 3 27 37), (.pair 3 4 226), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21507 / 12800) (.cycle 0 [(.pair 0 1 293), (.pair 1 2 258), (.support 2 3 27 37), (.pair 3 4 223), (.support 4 0 40 41)]) (.split 2 (4383 / 2560) (.cycle 0 [(.pair 0 1 270), (.pair 1 2 277), (.support 2 3 27 37), (.pair 3 4 223), (.support 4 0 40 41)]) (.cycle 0 [(.pair 0 1 270), (.pair 1 2 230), (.support 2 3 47 37), (.pair 3 4 223), (.support 4 0 40 41)]))) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 230), (.support 2 3 27 37), (.pair 3 4 223), (.support 4 0 40 46)]))) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 230), (.support 2 3 27 39), (.pair 3 4 227), (.pair 4 0 200)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 230), (.support 2 3 27 39), (.pair 3 4 192), (.support 4 0 40 41)]))) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.support 2 3 41 37), (.pair 3 4 226), (.pair 4 0 200)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.support 2 3 41 37), (.pair 3 4 223), (.support 4 0 40 41)])) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.support 2 3 41 39), (.pair 3 4 192), (.pair 4 0 185)]))) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 271), (.support 2 3 27 37), (.pair 3 4 226), (.pair 4 0 270)]) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 201), (.support 2 3 27 37), (.pair 3 4 226), (.pair 4 0 270)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 201), (.support 2 3 27 37), (.pair 3 4 226), (.pair 4 0 200)])) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (4383 / 2560) (.split 3 (21711 / 12800) (.split 4 (21609 / 12800) (.inner ![262, 272, 278, 243, 262]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 272), (.support 2 3 27 37), (.pair 3 4 248), (.support 4 0 45 41)])) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 272), (.support 2 3 27 44), (.pair 3 4 223), (.support 4 0 40 41)])) (.split 3 (21711 / 12800) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 271), (.support 2 3 47 37), (.pair 3 4 248), (.support 4 0 40 41)]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 271), (.support 2 3 47 44), (.pair 3 4 223), (.support 4 0 40 41)]))) (.split 2 (4383 / 2560) (.split 3 (21711 / 12800) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 273), (.support 2 3 27 37), (.pair 3 4 248), (.support 4 0 40 41)]) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 273), (.support 2 3 27 44), (.pair 3 4 223), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 45), (.support 1 2 45 47), (.support 2 3 47 37), (.pair 3 4 223), (.support 4 0 40 41)]))) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 201), (.support 2 3 27 37), (.pair 3 4 223), (.support 4 0 40 46)]))) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.support 2 3 27 39), (.pair 3 4 227), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (4383 / 2560) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 272), (.support 2 3 27 39), (.pair 3 4 192), (.support 4 0 40 41)]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 271), (.support 2 3 47 39), (.pair 3 4 192), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 201), (.support 2 3 27 39), (.pair 3 4 192), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 201), (.support 2 3 27 39), (.pair 3 4 192), (.support 4 0 40 46)])))) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.support 2 3 41 37), (.pair 3 4 226), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.support 2 3 41 37), (.pair 3 4 223), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.support 2 3 41 39), (.pair 3 4 192), (.pair 4 0 185)]))))) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.split 4 (10881 / 6400) (.split 0 (4383 / 2560) (.cycle 0 [(.pair 0 1 277), (.pair 1 2 230), (.support 2 3 27 37), (.pair 3 4 225), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 230), (.support 2 3 27 37), (.pair 3 4 225), (.support 4 0 37 47)])) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 230), (.support 2 3 27 37), (.pair 3 4 195), (.support 4 0 39 27)])) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 230), (.support 2 3 27 39), (.pair 3 4 195), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 230), (.support 2 3 27 39), (.support 3 4 39 39), (.support 4 0 39 27)]))) (.split 3 (10881 / 6400) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.support 2 3 41 37), (.pair 3 4 225), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.support 2 3 41 37), (.pair 3 4 195), (.support 4 0 39 27)])) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.support 2 3 41 39), (.pair 3 4 170), (.support 4 0 37 27)]))) (.split 2 (10983 / 6400) .local (.split 3 (10881 / 6400) (.split 4 (10881 / 6400) (.split 0 (4383 / 2560) (.split 1 (21609 / 12800) (.cycle 0 [(.pair 0 1 272), (.support 1 2 40 41), (.support 2 3 41 37), (.pair 3 4 225), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 273), (.support 1 2 45 41), (.support 2 3 41 37), (.pair 3 4 225), (.support 4 0 37 27)])) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.support 2 3 41 37), (.pair 3 4 225), (.support 4 0 37 47)])) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.support 2 3 41 37), (.pair 3 4 195), (.support 4 0 39 27)])) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.support 2 3 41 39), (.pair 3 4 195), (.support 4 0 37 27)]) (.outer ![27, 40, 41, 39, 39]))))) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 230), (.support 2 3 27 37), (.pair 3 4 225), (.support 4 0 37 41)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 230), (.support 2 3 27 37), (.pair 3 4 195), (.support 4 0 39 41)])) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 230), (.support 2 3 27 39), (.pair 3 4 170), (.support 4 0 37 41)])) (.split 3 (10881 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.support 2 3 41 37), (.pair 3 4 195), (.support 4 0 37 41)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.support 2 3 41 39), (.pair 3 4 170), (.support 4 0 37 41)]))) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.split 4 (10881 / 6400) (.split 0 (22017 / 12800) (.split 1 (21609 / 12800) (.split 2 (4383 / 2560) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 272), (.support 2 3 27 37), (.pair 3 4 225), (.support 4 0 37 41)]) (.cycle 0 [(.pair 0 1 262), (.pair 1 2 271), (.support 2 3 47 37), (.pair 3 4 225), (.support 4 0 37 41)])) (.cycle 0 [(.support 0 1 41 45), (.pair 1 2 201), (.support 2 3 27 37), (.pair 3 4 225), (.support 4 0 37 41)])) (.cycle 0 [(.support 0 1 46 40), (.pair 1 2 201), (.support 2 3 27 37), (.pair 3 4 225), (.support 4 0 37 46)])) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.support 2 3 27 37), (.pair 3 4 195), (.support 4 0 39 41)])) (.split 4 (10881 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.support 2 3 27 39), (.pair 3 4 195), (.support 4 0 37 41)]) (.outer ![41, 40, 27, 39, 39]))) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.support 2 3 41 37), (.pair 3 4 195), (.support 4 0 37 41)]) (.outer ![41, 40, 41, 39, 37]))))))) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (2217 / 1280) (.split 3 (10779 / 6400) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 228), (.pair 4 0 201)]) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 36), (.support 2 3 36 40), (.pair 3 4 222), (.pair 4 0 201)])) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 34), (.support 2 3 34 28), (.pair 3 4 222), (.pair 4 0 201)])) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 36), (.support 2 3 36 28), (.pair 3 4 222), (.pair 4 0 201)])) (.split 1 (10779 / 6400) (.split 2 (2217 / 1280) (.split 3 (10779 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 231), (.pair 4 0 200)]) (.split 0 (22017 / 12800) (.cycle 0 [(.pair 0 1 270), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 228), (.support 4 0 40 41)]) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 228), (.support 4 0 40 46)]))) (.split 4 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 36), (.support 2 3 36 40), (.pair 3 4 228), (.pair 4 0 200)]) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 36), (.support 2 3 36 40), (.pair 3 4 222), (.support 4 0 40 41)]))) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 34), (.support 2 3 34 28), (.pair 3 4 222), (.pair 4 0 185)])) (.split 2 (2217 / 1280) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 36), (.support 2 3 36 28), (.pair 3 4 228), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 36), (.support 2 3 36 40), (.pair 3 4 222), (.pair 4 0 185)])) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 34), (.support 2 3 34 28), (.pair 3 4 222), (.pair 4 0 185)])))) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (2217 / 1280) (.split 3 (10779 / 6400) (.split 4 (10881 / 6400) (.split 0 (4383 / 2560) (.cycle 0 [(.pair 0 1 277), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 226), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 226), (.support 4 0 37 47)])) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 227), (.support 4 0 39 27)])) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 36), (.support 2 3 36 40), (.pair 3 4 223), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 36), (.support 2 3 36 40), (.pair 3 4 192), (.support 4 0 39 27)]))) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 34), (.support 2 3 34 28), (.pair 3 4 192), (.support 4 0 37 27)])) (.split 2 (2217 / 1280) (.split 3 (10779 / 6400) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 36), (.support 2 3 36 28), (.pair 3 4 226), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 36), (.support 2 3 36 28), (.pair 3 4 227), (.support 4 0 39 27)])) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 36), (.support 2 3 36 40), (.pair 3 4 192), (.support 4 0 37 27)])) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 34), (.support 2 3 34 28), (.pair 3 4 192), (.support 4 0 37 27)]))) (.split 1 (10779 / 6400) (.split 2 (2217 / 1280) (.split 3 (10779 / 6400) (.split 4 (10881 / 6400) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 226), (.support 4 0 37 41)]) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 227), (.support 4 0 39 41)])) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 36), (.support 2 3 36 40), (.pair 3 4 192), (.support 4 0 37 41)])) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 34), (.support 2 3 34 28), (.pair 3 4 192), (.support 4 0 37 41)])) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 36), (.support 2 3 36 28), (.pair 3 4 192), (.support 4 0 37 41)])))) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.cycle 0 [(.pair 0 1 201), (.support 1 2 28 36), (.support 2 3 36 37), (.pair 3 4 192), (.pair 4 0 201)]) (.split 1 (10779 / 6400) (.split 2 (2217 / 1280) (.split 3 (10881 / 6400) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 36), (.support 2 3 36 37), (.pair 3 4 223), (.pair 4 0 185)]) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 36), (.support 2 3 36 39), (.pair 3 4 192), (.pair 4 0 185)])) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 34), (.support 2 3 34 37), (.pair 3 4 192), (.pair 4 0 185)])) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 36), (.support 2 3 36 37), (.pair 3 4 192), (.pair 4 0 185)]))) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (2217 / 1280) (.split 3 (10881 / 6400) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 36), (.support 2 3 36 37), (.pair 3 4 195), (.support 4 0 37 27)]) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 36), (.support 2 3 36 39), (.pair 3 4 170), (.support 4 0 37 27)])) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 34), (.support 2 3 34 37), (.pair 3 4 170), (.support 4 0 37 27)])) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 36), (.support 2 3 36 37), (.pair 3 4 170), (.support 4 0 37 27)])) (.split 1 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 36), (.support 2 3 36 37), (.pair 3 4 170), (.support 4 0 37 41)]) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 36), (.support 2 3 36 37), (.pair 3 4 170), (.support 4 0 37 41)])))))) (.split 2 (5517 / 3200) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10983 / 6400) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 27), (.pair 2 3 230), (.pair 3 4 228), (.pair 4 0 201)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 27), (.pair 2 3 201), (.pair 3 4 228), (.pair 4 0 230)]) .local)) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 41), (.pair 2 3 185), (.pair 3 4 222), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 27 39), (.support 1 2 39 27), (.pair 2 3 185), (.pair 3 4 222), (.pair 4 0 201)])) (.split 1 (10881 / 6400) (.split 2 (10983 / 6400) (.cycle 0 [(.support 0 1 41 37), (.support 1 2 37 27), (.pair 2 3 201), (.pair 3 4 222), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 41 37), (.support 1 2 37 41), (.pair 2 3 185), (.pair 3 4 222), (.pair 4 0 185)])) (.cycle 0 [(.support 0 1 41 39), (.support 1 2 39 27), (.pair 2 3 185), (.pair 3 4 222), (.pair 4 0 185)]))) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10983 / 6400) (.split 3 (10779 / 6400) (.split 4 (10881 / 6400) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 27), (.pair 2 3 230), (.pair 3 4 226), (.support 4 0 37 27)]) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 27), (.pair 2 3 230), (.pair 3 4 227), (.support 4 0 39 27)])) .local) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 41), (.pair 2 3 200), (.pair 3 4 227), (.support 4 0 37 27)]) (.split 4 (10881 / 6400) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 41), (.support 2 3 41 40), (.pair 3 4 223), (.support 4 0 37 27)]) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 41), (.support 2 3 41 40), (.pair 3 4 192), (.support 4 0 39 27)])))) (.cycle 0 [(.support 0 1 27 39), (.support 1 2 39 27), (.pair 2 3 185), (.pair 3 4 192), (.support 4 0 37 27)])) (.cycle 0 [(.support 0 1 41 37), (.support 1 2 37 27), (.pair 2 3 185), (.pair 3 4 192), (.support 4 0 37 41)]))) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 27), (.support 2 3 27 37), (.pair 3 4 226), (.pair 4 0 230)]) .local) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 27), (.support 2 3 27 39), (.pair 3 4 227), (.pair 4 0 230)]) .local)) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 41), (.support 2 3 41 37), (.pair 3 4 192), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 27 39), (.support 1 2 39 27), (.support 2 3 27 37), (.pair 3 4 192), (.pair 4 0 201)])) (.split 1 (10881 / 6400) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 37), (.support 1 2 37 27), (.support 2 3 27 37), (.pair 3 4 226), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 37), (.support 1 2 37 27), (.support 2 3 27 37), (.pair 3 4 223), (.support 4 0 40 41)])) (.cycle 0 [(.support 0 1 41 37), (.support 1 2 37 27), (.support 2 3 27 39), (.pair 3 4 192), (.pair 4 0 185)])) (.cycle 0 [(.support 0 1 41 37), (.support 1 2 37 41), (.support 2 3 41 37), (.pair 3 4 192), (.pair 4 0 185)])) (.cycle 0 [(.support 0 1 41 39), (.support 1 2 39 27), (.support 2 3 27 37), (.pair 3 4 192), (.pair 4 0 185)]))) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10983 / 6400) .local (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 41), (.support 2 3 41 37), (.pair 3 4 195), (.support 4 0 37 27)]) (.outer ![27, 37, 41, 39, 37]))) (.split 2 (10983 / 6400) .local (.outer ![27, 39, 41, 37, 37]))) (.split 1 (10881 / 6400) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 41 37), (.support 1 2 37 27), (.support 2 3 27 37), (.pair 3 4 195), (.support 4 0 37 41)]) (.outer ![41, 37, 27, 39, 37])) (.outer ![41, 37, 41, 37, 37])) (.outer ![41, 39, 27, 37, 37]))))) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 36), (.support 2 3 36 28), (.pair 3 4 222), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 36), (.support 2 3 36 28), (.pair 3 4 192), (.support 4 0 37 27)])) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 36), (.support 2 3 36 37), (.pair 3 4 192), (.pair 4 0 185)]) (.outer ![27, 37, 36, 37, 37]))))) (.split 1 (1083 / 640) (.split 2 (5517 / 3200) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 230), (.pair 2 3 230), (.pair 3 4 228), (.support 4 0 28 36)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 230), (.pair 2 3 201), (.pair 3 4 228), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 230), (.pair 2 3 201), (.pair 3 4 222), (.support 4 0 40 36)]))) (.split 3 (10779 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 200), (.pair 2 3 200), (.pair 3 4 231), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 200), (.pair 2 3 200), (.pair 3 4 228), (.support 4 0 40 36)])) (.split 4 (10779 / 6400) (.split 0 (22119 / 12800) (.split 1 (21507 / 12800) (.cycle 0 [(.pair 0 1 287), (.pair 1 2 237), (.support 2 3 41 40), (.pair 3 4 228), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 42), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 228), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 48 28), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 228), (.support 4 0 28 48)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 222), (.support 4 0 40 36)])))) (.split 2 (10983 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 201), (.pair 2 3 201), (.pair 3 4 222), (.support 4 0 28 36)]) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 36 40), (.support 1 2 40 41), (.pair 2 3 200), (.pair 3 4 228), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 40), (.support 1 2 40 41), (.support 2 3 41 40), (.pair 3 4 222), (.support 4 0 28 36)])))) (.cycle 0 [(.support 0 1 34 28), (.pair 1 2 185), (.pair 2 3 185), (.pair 3 4 222), (.support 4 0 28 34)])) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 230), (.pair 2 3 201), (.pair 3 4 192), (.support 4 0 37 36)]) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 200), (.pair 2 3 200), (.pair 3 4 227), (.support 4 0 37 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 192), (.support 4 0 37 36)]))) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 185), (.pair 2 3 185), (.pair 3 4 192), (.support 4 0 37 36)])) (.cycle 0 [(.support 0 1 34 28), (.pair 1 2 185), (.pair 2 3 185), (.pair 3 4 192), (.support 4 0 37 34)]))) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.split 0 (22119 / 12800) (.split 1 (21507 / 12800) (.cycle 0 [(.pair 0 1 287), (.pair 1 2 258), (.support 2 3 27 37), (.pair 3 4 226), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 42), (.pair 1 2 230), (.support 2 3 27 37), (.pair 3 4 226), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 48 28), (.pair 1 2 230), (.support 2 3 27 37), (.pair 3 4 226), (.support 4 0 28 48)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 230), (.support 2 3 27 37), (.pair 3 4 223), (.support 4 0 40 36)])) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 230), (.support 2 3 27 39), (.pair 3 4 227), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 230), (.support 2 3 27 39), (.pair 3 4 192), (.support 4 0 40 36)]))) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 200), (.support 2 3 41 37), (.pair 3 4 226), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 200), (.support 2 3 41 37), (.pair 3 4 223), (.support 4 0 40 36)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 200), (.support 2 3 41 39), (.pair 3 4 192), (.support 4 0 28 36)]))) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 201), (.support 2 3 27 37), (.pair 3 4 226), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 201), (.support 2 3 27 37), (.pair 3 4 223), (.support 4 0 40 36)])) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 201), (.support 2 3 27 39), (.pair 3 4 192), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 36 40), (.support 1 2 40 41), (.support 2 3 41 37), (.pair 3 4 192), (.support 4 0 28 36)]))) (.split 1 (10779 / 6400) (.cycle 0 [(.support 0 1 34 28), (.pair 1 2 200), (.support 2 3 27 37), (.pair 3 4 192), (.support 4 0 28 34)]) (.cycle 0 [(.support 0 1 34 40), (.pair 1 2 185), (.support 2 3 27 37), (.pair 3 4 192), (.support 4 0 28 34)]))) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 230), (.support 2 3 27 37), (.pair 3 4 195), (.support 4 0 37 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 230), (.support 2 3 27 39), (.pair 3 4 170), (.support 4 0 37 36)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 200), (.support 2 3 41 37), (.pair 3 4 170), (.support 4 0 37 36)])) (.split 2 (10983 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 201), (.support 2 3 27 37), (.pair 3 4 170), (.support 4 0 37 36)]) (.cycle 0 [(.support 0 1 36 40), (.support 1 2 40 41), (.support 2 3 41 37), (.pair 3 4 170), (.support 4 0 37 36)]))) (.cycle 0 [(.support 0 1 34 28), (.pair 1 2 185), (.support 2 3 27 37), (.pair 3 4 170), (.support 4 0 37 34)])))) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (2217 / 1280) (.split 3 (10779 / 6400) (.split 4 (10779 / 6400) (.split 0 (22119 / 12800) (.split 1 (21507 / 12800) (.cycle 0 [(.pair 0 1 287), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 231), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 42), (.support 1 2 42 36), (.support 2 3 36 28), (.pair 3 4 231), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 48 28), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 231), (.support 4 0 28 48)])) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 228), (.support 4 0 40 36)])) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 36), (.support 2 3 36 40), (.pair 3 4 228), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 36), (.support 2 3 36 40), (.pair 3 4 222), (.support 4 0 40 36)]))) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 34), (.support 2 3 34 28), (.pair 3 4 222), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 36 40), (.support 1 2 40 36), (.support 2 3 36 28), (.pair 3 4 222), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 34 28), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 222), (.support 4 0 28 34)])) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (2217 / 1280) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 227), (.support 4 0 37 36)]) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 36), (.support 2 3 36 40), (.pair 3 4 192), (.support 4 0 37 36)])) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 34), (.support 2 3 34 28), (.pair 3 4 192), (.support 4 0 37 36)])) (.cycle 0 [(.support 0 1 36 40), (.support 1 2 40 36), (.support 2 3 36 28), (.pair 3 4 192), (.support 4 0 37 36)])) (.cycle 0 [(.support 0 1 34 28), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 192), (.support 4 0 37 34)]))) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (2217 / 1280) (.split 3 (10881 / 6400) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 36), (.support 2 3 36 37), (.pair 3 4 223), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 36), (.support 2 3 36 39), (.pair 3 4 192), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 34), (.support 2 3 34 37), (.pair 3 4 192), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 36 40), (.support 1 2 40 36), (.support 2 3 36 37), (.pair 3 4 192), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 34 28), (.support 1 2 28 36), (.support 2 3 36 37), (.pair 3 4 192), (.support 4 0 28 34)])) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 36), (.support 2 3 36 37), (.pair 3 4 170), (.support 4 0 37 36)])))) (.split 2 (5517 / 3200) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 36 37), (.support 1 2 37 27), (.pair 2 3 185), (.pair 3 4 222), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 37), (.support 1 2 37 27), (.pair 2 3 185), (.pair 3 4 192), (.support 4 0 37 36)])) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 36 37), (.support 1 2 37 27), (.support 2 3 27 37), (.pair 3 4 192), (.support 4 0 28 36)]) (.outer ![36, 37, 27, 37, 37]))) (.cycle 0 [(.support 0 1 36 37), (.support 1 2 37 36), (.support 2 3 36 28), (.pair 3 4 170), (.support 4 0 28 36)])))) (.split 0 (5517 / 3200) (.split 1 (1083 / 640) (.split 2 (5517 / 3200) (.split 3 (1083 / 640) (.split 4 (5517 / 3200) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 230), (.pair 2 3 201), (.pair 3 4 185), (.support 4 0 27 27)]) (.split 3 (10779 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.pair 2 3 200), (.pair 3 4 200), (.support 4 0 27 27)]) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 185), (.support 4 0 27 27)]))) (.split 2 (10983 / 6400) (.split 3 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 201), (.pair 2 3 230), (.pair 3 4 200), (.support 4 0 27 27)]) (.split 4 (10983 / 6400) .local (.cycle 0 [(.pair 0 1 201), (.pair 1 2 201), (.pair 2 3 201), (.support 3 4 40 41), (.support 4 0 41 27)]))) (.split 3 (10779 / 6400) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.pair 2 3 200), (.pair 3 4 200), (.support 4 0 27 27)]) (.split 4 (10983 / 6400) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.support 2 3 41 40), (.pair 3 4 201), (.support 4 0 27 27)]) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.support 2 3 41 40), (.support 3 4 40 41), (.support 4 0 41 27)]))))) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 230), (.pair 2 3 201), (.pair 3 4 185), (.support 4 0 27 41)]) (.split 3 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.pair 2 3 200), (.pair 3 4 200), (.support 4 0 27 41)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.support 2 3 41 40), (.pair 3 4 185), (.support 4 0 27 41)]))) (.split 2 (10983 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.pair 2 3 201), (.pair 3 4 185), (.support 4 0 27 41)]) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.pair 2 3 200), (.pair 3 4 200), (.support 4 0 27 41)]) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.support 2 3 41 40), (.pair 3 4 185), (.support 4 0 27 41)]))))) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 185), (.pair 2 3 185), (.support 3 4 28 36), (.support 4 0 36 27)])) (.split 4 (5517 / 3200) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.support 2 3 27 37), (.support 3 4 37 27), (.support 4 0 27 27)]) (.split 2 (10983 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 201), (.support 2 3 27 37), (.support 3 4 37 27), (.support 4 0 27 27)]) (.outer ![27, 40, 41, 37, 27]))) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 185), (.support 2 3 27 37), (.support 3 4 37 27), (.support 4 0 27 41)])) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 185), (.support 2 3 27 37), (.support 3 4 37 36), (.support 4 0 36 27)]))) (.split 3 (1083 / 640) (.split 4 (5517 / 3200) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.split 2 (2217 / 1280) (.split 3 (10779 / 6400) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 200), (.support 4 0 27 27)]) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 36), (.support 2 3 36 40), (.pair 3 4 185), (.support 4 0 27 27)])) (.cycle 0 [(.pair 0 1 230), (.support 1 2 28 34), (.support 2 3 34 28), (.pair 3 4 185), (.support 4 0 27 27)])) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 36), (.support 2 3 36 28), (.pair 3 4 185), (.support 4 0 27 27)])) (.split 1 (10779 / 6400) (.cycle 0 [(.pair 0 1 200), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 185), (.support 4 0 27 41)]) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 36), (.support 2 3 36 28), (.pair 3 4 185), (.support 4 0 27 41)]))) (.cycle 0 [(.pair 0 1 185), (.support 1 2 28 36), (.support 2 3 36 28), (.support 3 4 28 36), (.support 4 0 36 27)])) (.cycle 0 [(.pair 0 1 185), (.support 1 2 28 36), (.support 2 3 36 37), (.support 3 4 37 27), (.support 4 0 27 27)]))) (.split 2 (5517 / 3200) (.split 3 (1083 / 640) (.split 4 (5517 / 3200) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10983 / 6400) (.split 3 (10779 / 6400) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 27), (.pair 2 3 230), (.pair 3 4 200), (.support 4 0 27 27)]) (.split 4 (10983 / 6400) .local (.outer ![27, 37, 27, 40, 41]))) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 41), (.pair 2 3 185), (.pair 3 4 185), (.support 4 0 27 27)])) (.cycle 0 [(.support 0 1 27 39), (.support 1 2 39 27), (.pair 2 3 185), (.pair 3 4 185), (.support 4 0 27 27)])) (.cycle 0 [(.support 0 1 41 37), (.support 1 2 37 27), (.pair 2 3 185), (.pair 3 4 185), (.support 4 0 27 41)])) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 27), (.pair 2 3 185), (.support 3 4 28 36), (.support 4 0 36 27)])) (.outer ![27, 37, 27, 37, 27])) (.split 3 (1083 / 640) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 36), (.support 2 3 36 28), (.pair 3 4 187), (.support 4 0 27 27)]) (.outer ![27, 37, 36, 37, 27])))) (.split 1 (1083 / 640) (.split 2 (5517 / 3200) (.split 3 (1083 / 640) (.split 4 (5517 / 3200) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 185), (.pair 2 3 185), (.pair 3 4 185), (.support 4 0 27 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 185), (.pair 2 3 185), (.support 3 4 28 36), (.support 4 0 36 36)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 185), (.support 2 3 27 37), (.support 3 4 37 27), (.support 4 0 27 36)])) (.split 3 (1083 / 640) (.split 4 (5517 / 3200) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 36), (.support 2 3 36 28), (.pair 3 4 185), (.support 4 0 27 36)]) (.outer ![36, 28, 36, 28, 36])) (.outer ![36, 28, 36, 37, 27]))) (.split 2 (5517 / 3200) (.cycle 0 [(.support 0 1 36 37), (.support 1 2 37 27), (.pair 2 3 183), (.support 3 4 28 27), (.support 4 0 27 36)]) (.outer ![36, 37, 36, 28, 27]))))) (.split 4 (2733 / 1600) (.split 0 (5517 / 3200) (.split 1 (1083 / 640) (.split 2 (5517 / 3200) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.support 2 3 27 27), (.pair 3 4 185), (.pair 4 0 201)]) (.split 2 (10983 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 201), (.support 2 3 27 27), (.pair 3 4 201), (.pair 4 0 201)]) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 201), (.support 2 3 27 41), (.pair 3 4 185), (.pair 4 0 201)])) (.cycle 0 [(.pair 0 1 201), (.support 1 2 40 41), (.support 2 3 41 27), (.pair 3 4 185), (.pair 4 0 201)]))) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 230), (.support 2 3 27 27), (.pair 3 4 201), (.pair 4 0 185)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 230), (.support 2 3 27 41), (.pair 3 4 185), (.pair 4 0 185)])) (.split 3 (10983 / 6400) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.support 2 3 41 27), (.pair 3 4 201), (.pair 4 0 185)]) (.cycle 0 [(.pair 0 1 200), (.pair 1 2 200), (.support 2 3 41 41), (.pair 3 4 185), (.pair 4 0 185)]))) (.split 2 (10983 / 6400) (.split 3 (10983 / 6400) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.support 2 3 27 27), (.pair 3 4 230), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.support 2 3 27 27), (.pair 3 4 201), (.support 4 0 40 41)])) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.support 2 3 27 41), (.pair 3 4 200), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 40), (.pair 1 2 201), (.support 2 3 27 41), (.support 3 4 41 40), (.support 4 0 40 41)]))) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.support 2 3 41 27), (.pair 3 4 201), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 41 40), (.support 1 2 40 41), (.support 2 3 41 41), (.pair 3 4 185), (.pair 4 0 185)]))))) (.split 0 (10983 / 6400) (.split 1 (10779 / 6400) (.cycle 0 [(.pair 0 1 230), (.pair 1 2 200), (.support 2 3 27 27), (.support 3 4 27 37), (.support 4 0 37 27)]) (.split 2 (10983 / 6400) (.cycle 0 [(.pair 0 1 201), (.pair 1 2 201), (.support 2 3 27 27), (.support 3 4 27 37), (.support 4 0 37 27)]) (.outer ![27, 40, 41, 27, 37]))) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 185), (.support 2 3 27 27), (.support 3 4 27 37), (.support 4 0 37 41)]))) (.split 4 (1083 / 640) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 185), (.support 2 3 27 36), (.support 3 4 36 28), (.pair 4 0 185)]) (.cycle 0 [(.pair 0 1 185), (.pair 1 2 185), (.support 2 3 27 36), (.support 3 4 36 37), (.support 4 0 37 27)]))) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.cycle 0 [(.pair 0 1 185), (.support 1 2 28 36), (.support 2 3 36 27), (.pair 3 4 185), (.pair 4 0 185)]) (.cycle 0 [(.pair 0 1 185), (.support 1 2 28 36), (.support 2 3 36 27), (.support 3 4 27 37), (.support 4 0 37 27)])) (.cycle 0 [(.pair 0 1 185), (.support 1 2 28 36), (.support 2 3 36 36), (.support 3 4 36 28), (.pair 4 0 183)]))) (.split 2 (5517 / 3200) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10881 / 6400) (.split 2 (10983 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 27), (.support 2 3 27 27), (.pair 3 4 201), (.pair 4 0 201)]) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 27), (.support 2 3 27 41), (.pair 3 4 185), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 41), (.support 2 3 41 27), (.pair 3 4 185), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 27 39), (.support 1 2 39 27), (.support 2 3 27 27), (.pair 3 4 185), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 41 37), (.support 1 2 37 27), (.support 2 3 27 27), (.pair 3 4 185), (.pair 4 0 185)])) (.outer ![27, 37, 27, 27, 37])) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 27), (.support 2 3 27 36), (.support 3 4 36 28), (.pair 4 0 183)])) (.cycle 0 [(.support 0 1 27 37), (.support 1 2 37 36), (.support 2 3 36 27), (.support 3 4 27 28), (.pair 4 0 183)]))) (.split 1 (1083 / 640) (.split 2 (5517 / 3200) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (2217 / 1280) (.split 1 (10779 / 6400) (.split 2 (10983 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 230), (.support 2 3 27 27), (.pair 3 4 201), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 230), (.support 2 3 27 41), (.pair 3 4 185), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 200), (.support 2 3 41 27), (.pair 3 4 185), (.support 4 0 28 36)])) (.split 2 (10983 / 6400) (.cycle 0 [(.support 0 1 36 40), (.pair 1 2 201), (.support 2 3 27 27), (.pair 3 4 185), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 40), (.support 1 2 40 41), (.support 2 3 41 27), (.pair 3 4 185), (.support 4 0 28 36)]))) (.cycle 0 [(.support 0 1 34 28), (.pair 1 2 185), (.support 2 3 27 27), (.pair 3 4 185), (.support 4 0 28 34)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 185), (.support 2 3 27 27), (.support 3 4 27 37), (.support 4 0 37 36)])) (.cycle 0 [(.support 0 1 36 28), (.pair 1 2 185), (.support 2 3 27 36), (.support 3 4 36 28), (.support 4 0 28 36)])) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 36 28), (.support 1 2 28 36), (.support 2 3 36 27), (.pair 3 4 185), (.support 4 0 28 36)]) (.outer ![36, 28, 36, 27, 37])) (.outer ![36, 28, 36, 36, 28]))) (.split 2 (5517 / 3200) (.split 3 (5517 / 3200) (.cycle 0 [(.support 0 1 36 37), (.support 1 2 37 27), (.support 2 3 27 27), (.pair 3 4 183), (.support 4 0 28 36)]) (.outer ![36, 37, 27, 36, 28])) (.outer ![36, 37, 36, 27, 28])))) (.outer ![27, 28, 27, 27, 27])))) (.split 2 (2733 / 1600) (.split 3 (2733 / 1600) (.split 4 (2733 / 1600) (.split 0 (5517 / 3200) (.split 1 (5517 / 3200) (.split 2 (1083 / 640) (.split 3 (1083 / 640) (.cycle 0 [(.support 0 1 27 27), (.pair 1 2 185), (.pair 2 3 222), (.pair 3 4 192), (.pair 4 0 183)]) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 27 27), (.pair 1 2 185), (.pair 2 3 192), (.pair 3 4 192), (.pair 4 0 185)]) (.split 0 (10983 / 6400) (.split 1 (10983 / 6400) (.cycle 0 [(.support 0 1 27 27), (.pair 1 2 201), (.pair 2 3 192), (.pair 3 4 170), (.support 4 0 37 27)]) (.cycle 0 [(.support 0 1 27 41), (.pair 1 2 185), (.pair 2 3 192), (.pair 3 4 170), (.support 4 0 37 27)])) (.cycle 0 [(.support 0 1 41 27), (.pair 1 2 185), (.pair 2 3 192), (.pair 3 4 170), (.support 4 0 37 41)])))) (.split 3 (1083 / 640) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 27 27), (.support 1 2 27 37), (.pair 2 3 192), (.pair 3 4 222), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 27 27), (.support 1 2 27 37), (.pair 2 3 192), (.pair 3 4 192), (.support 4 0 37 27)])) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.cycle 0 [(.support 0 1 27 27), (.support 1 2 27 37), (.pair 2 3 170), (.pair 3 4 192), (.pair 4 0 201)]) (.cycle 0 [(.support 0 1 41 27), (.support 1 2 27 37), (.pair 2 3 170), (.pair 3 4 192), (.pair 4 0 185)])) (.split 0 (10983 / 6400) (.split 1 (10983 / 6400) .local (.cycle 0 [(.support 0 1 27 41), (.support 1 2 41 37), (.pair 2 3 170), (.pair 3 4 170), (.support 4 0 37 27)])) (.cycle 0 [(.support 0 1 41 27), (.support 1 2 27 37), (.pair 2 3 170), (.pair 3 4 170), (.support 4 0 37 41)]))))) (.split 2 (1083 / 640) (.cycle 0 [(.support 0 1 27 36), (.support 1 2 36 28), (.pair 2 3 192), (.pair 3 4 170), (.pair 4 0 183)]) (.cycle 0 [(.support 0 1 27 36), (.support 1 2 36 37), (.pair 2 3 170), (.pair 3 4 170), (.pair 4 0 183)]))) (.split 1 (5517 / 3200) (.split 2 (1083 / 640) (.cycle 0 [(.support 0 1 36 27), (.pair 1 2 185), (.pair 2 3 192), (.pair 3 4 170), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 27), (.support 1 2 27 37), (.pair 2 3 170), (.pair 3 4 170), (.support 4 0 28 36)])) (.cycle 0 [(.support 0 1 36 36), (.support 1 2 36 28), (.pair 2 3 170), (.pair 3 4 170), (.support 4 0 28 36)]))) (.split 0 (5517 / 3200) (.split 1 (5517 / 3200) (.split 2 (1083 / 640) (.cycle 0 [(.support 0 1 27 27), (.pair 1 2 185), (.pair 2 3 192), (.support 3 4 28 27), (.support 4 0 27 27)]) (.split 3 (1083 / 640) (.cycle 0 [(.support 0 1 27 27), (.support 1 2 27 37), (.pair 2 3 192), (.pair 3 4 187), (.support 4 0 27 27)]) (.outer ![27, 27, 37, 37, 27]))) (.cycle 0 [(.support 0 1 27 36), (.support 1 2 36 28), (.pair 2 3 170), (.support 3 4 28 27), (.support 4 0 27 27)])) (.cycle 0 [(.support 0 1 36 27), (.support 1 2 27 28), (.pair 2 3 170), (.support 3 4 28 27), (.support 4 0 27 36)]))) (.split 4 (2733 / 1600) (.split 0 (5517 / 3200) (.split 1 (5517 / 3200) (.split 2 (1083 / 640) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10983 / 6400) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 27 27), (.pair 1 2 230), (.pair 2 3 200), (.pair 3 4 185), (.pair 4 0 201)]) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 27 27), (.pair 1 2 201), (.pair 2 3 201), (.pair 3 4 201), (.pair 4 0 201)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 27 27), (.pair 1 2 201), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 230)]) (.cycle 0 [(.support 0 1 27 27), (.pair 1 2 201), (.support 2 3 40 41), (.support 3 4 41 40), (.pair 4 0 201)])))) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 27 41), (.pair 1 2 200), (.pair 2 3 200), (.pair 3 4 185), (.pair 4 0 201)]) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 27 41), (.support 1 2 41 40), (.pair 2 3 201), (.pair 3 4 201), (.pair 4 0 201)]) (.cycle 0 [(.support 0 1 27 41), (.support 1 2 41 40), (.support 2 3 40 41), (.pair 3 4 185), (.pair 4 0 201)])))) (.split 1 (10983 / 6400) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 41 27), (.pair 1 2 230), (.pair 2 3 200), (.pair 3 4 185), (.pair 4 0 185)]) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 41 27), (.pair 1 2 201), (.pair 2 3 201), (.pair 3 4 201), (.pair 4 0 185)]) (.split 4 (10779 / 6400) (.cycle 0 [(.support 0 1 41 27), (.pair 1 2 201), (.support 2 3 40 41), (.pair 3 4 200), (.pair 4 0 200)]) (.cycle 0 [(.support 0 1 41 27), (.pair 1 2 201), (.support 2 3 40 41), (.support 3 4 41 40), (.support 4 0 40 41)])))) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 41 41), (.pair 1 2 200), (.pair 2 3 200), (.pair 3 4 185), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 41 41), (.support 1 2 41 40), (.pair 2 3 185), (.pair 3 4 185), (.pair 4 0 185)])))) (.split 0 (10983 / 6400) (.split 1 (10983 / 6400) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 27 27), (.pair 1 2 230), (.pair 2 3 200), (.support 3 4 27 37), (.support 4 0 37 27)]) (.split 3 (10983 / 6400) .local (.outer ![27, 27, 40, 41, 37]))) (.cycle 0 [(.support 0 1 27 41), (.pair 1 2 185), (.pair 2 3 185), (.support 3 4 27 37), (.support 4 0 37 27)])) (.cycle 0 [(.support 0 1 41 27), (.pair 1 2 185), (.pair 2 3 185), (.support 3 4 27 37), (.support 4 0 37 41)]))) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10983 / 6400) (.split 2 (10779 / 6400) (.cycle 0 [(.support 0 1 27 27), (.pair 1 2 230), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 201)]) (.cycle 0 [(.support 0 1 27 27), (.pair 1 2 201), (.support 2 3 40 36), (.support 3 4 36 28), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 27 41), (.pair 1 2 185), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 201)])) (.split 1 (10983 / 6400) (.cycle 0 [(.support 0 1 41 27), (.pair 1 2 201), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 41 41), (.pair 1 2 185), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 185)]))) (.cycle 0 [(.support 0 1 27 27), (.pair 1 2 185), (.support 2 3 28 36), (.support 3 4 36 37), (.support 4 0 37 27)]))) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.split 0 (10983 / 6400) (.split 1 (10983 / 6400) (.split 2 (10881 / 6400) (.split 3 (10983 / 6400) (.cycle 0 [(.support 0 1 27 27), (.support 1 2 27 37), (.support 2 3 37 27), (.pair 3 4 201), (.pair 4 0 201)]) (.cycle 0 [(.support 0 1 27 27), (.support 1 2 27 37), (.support 2 3 37 41), (.pair 3 4 185), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 27 27), (.support 1 2 27 39), (.support 2 3 39 27), (.pair 3 4 185), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 27 41), (.support 1 2 41 37), (.support 2 3 37 27), (.pair 3 4 185), (.pair 4 0 201)])) (.cycle 0 [(.support 0 1 41 27), (.support 1 2 27 37), (.support 2 3 37 27), (.pair 3 4 185), (.pair 4 0 185)])) (.outer ![27, 27, 37, 27, 37])) (.cycle 0 [(.support 0 1 27 27), (.support 1 2 27 37), (.support 2 3 37 36), (.support 3 4 36 28), (.pair 4 0 183)]))) (.split 2 (1083 / 640) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 27 36), (.support 1 2 36 28), (.pair 2 3 185), (.pair 3 4 185), (.pair 4 0 185)]) (.cycle 0 [(.support 0 1 27 36), (.support 1 2 36 28), (.pair 2 3 185), (.support 3 4 27 37), (.support 4 0 37 27)])) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 27 36), (.support 1 2 36 28), (.support 2 3 28 36), (.support 3 4 36 28), (.pair 4 0 185)]) (.outer ![27, 36, 28, 36, 37]))) (.cycle 0 [(.support 0 1 27 36), (.support 1 2 36 37), (.support 2 3 37 27), (.support 3 4 27 28), (.pair 4 0 183)]))) (.split 1 (5517 / 3200) (.split 2 (1083 / 640) (.split 3 (5517 / 3200) (.split 4 (1083 / 640) (.cycle 0 [(.support 0 1 36 27), (.pair 1 2 185), (.pair 2 3 185), (.pair 3 4 185), (.support 4 0 28 36)]) (.cycle 0 [(.support 0 1 36 27), (.pair 1 2 185), (.pair 2 3 185), (.support 3 4 27 37), (.support 4 0 37 36)])) (.cycle 0 [(.support 0 1 36 27), (.pair 1 2 185), (.support 2 3 28 36), (.support 3 4 36 28), (.support 4 0 28 36)])) (.split 3 (5517 / 3200) (.cycle 0 [(.support 0 1 36 27), (.support 1 2 27 37), (.support 2 3 37 27), (.pair 3 4 183), (.support 4 0 28 36)]) (.outer ![36, 27, 37, 36, 28]))) (.split 2 (1083 / 640) (.split 3 (5517 / 3200) (.cycle 0 [(.support 0 1 36 36), (.support 1 2 36 28), (.pair 2 3 185), (.pair 3 4 183), (.support 4 0 28 36)]) (.outer ![36, 36, 28, 36, 28])) (.outer ![36, 36, 37, 27, 28])))) (.outer ![27, 27, 28, 27, 27]))) (.split 3 (2733 / 1600) (.split 4 (2733 / 1600) (.split 0 (5517 / 3200) (.split 1 (5517 / 3200) (.split 2 (5517 / 3200) (.split 3 (1083 / 640) (.cycle 0 [(.support 0 1 27 27), (.support 1 2 27 27), (.pair 2 3 185), (.pair 3 4 192), (.pair 4 0 183)]) (.cycle 0 [(.support 0 1 27 27), (.support 1 2 27 27), (.support 2 3 27 37), (.pair 3 4 170), (.pair 4 0 183)])) (.cycle 0 [(.support 0 1 27 27), (.support 1 2 27 36), (.support 2 3 36 28), (.pair 3 4 170), (.pair 4 0 183)])) (.cycle 0 [(.support 0 1 27 36), (.support 1 2 36 27), (.support 2 3 27 28), (.pair 3 4 170), (.pair 4 0 183)])) (.cycle 0 [(.support 0 1 36 27), (.support 1 2 27 27), (.support 2 3 27 28), (.pair 3 4 170), (.support 4 0 28 36)])) (.outer ![27, 27, 27, 28, 27])) (.outer ![27, 27, 27, 27, 28]))))

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk33Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk33Box k10p15chunk33Tree = true := by
  apply k10ModelCoverCheck_split_true
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
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · decide +kernel
                  · apply k10ModelCoverCheck_split_true
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
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
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
                            · decide +kernel
                            · decide +kernel
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
                                · decide +kernel
                              · decide +kernel
                        · apply k10ModelCoverCheck_split_true
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
                                · decide +kernel
                              · decide +kernel
                          · apply k10ModelCoverCheck_split_true
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
                                    · decide +kernel
                                  · apply k10ModelCoverCheck_split_true
                                    · decide +kernel
                                    · decide +kernel
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
                          · apply k10ModelCoverCheck_split_true
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
                      · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
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
                                  · decide +kernel
                                · decide +kernel
                              · decide +kernel
                            · decide +kernel
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
                    · decide +kernel
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · decide +kernel
                      · apply k10ModelCoverCheck_split_true
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
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
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
                          · apply k10ModelCoverCheck_split_true
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
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
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
                            · decide +kernel
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
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
                    · decide +kernel
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
                        · decide +kernel
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
                                · decide +kernel
                                · decide +kernel
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
                    · decide +kernel
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
          · apply k10ModelCoverCheck_split_true
            · apply k10ModelCoverCheck_split_true
              · decide +kernel
              · apply k10ModelCoverCheck_split_true
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
                            · decide +kernel
                            · apply k10ModelCoverCheck_split_true
                              · decide +kernel
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
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
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
                            · decide +kernel
                            · decide +kernel
                        · apply k10ModelCoverCheck_split_true
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
                                · decide +kernel
                              · decide +kernel
                          · apply k10ModelCoverCheck_split_true
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
                                · decide +kernel
                              · decide +kernel
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
                      · decide +kernel
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
                              · decide +kernel
                              · decide +kernel
                            · decide +kernel
                          · decide +kernel
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
                                · decide +kernel
                                · apply k10ModelCoverCheck_split_true
                                  · decide +kernel
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
                          · apply k10ModelCoverCheck_split_true
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
                                    · decide +kernel
                                  · apply k10ModelCoverCheck_split_true
                                    · decide +kernel
                                    · decide +kernel
                                · apply k10ModelCoverCheck_split_true
                                  · apply k10ModelCoverCheck_split_true
                                    · decide +kernel
                                    · decide +kernel
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
                                · apply k10ModelCoverCheck_split_true
                                  · decide +kernel
                                  · decide +kernel
                                · decide +kernel
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
                          · decide +kernel
                          · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · decide +kernel
                · apply k10ModelCoverCheck_split_true
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
                              · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                          · apply k10ModelCoverCheck_split_true
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
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
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
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
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
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
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
                              · decide +kernel
                            · decide +kernel
                          · apply k10ModelCoverCheck_split_true
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
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
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
                        · decide +kernel
                      · decide +kernel
                    · apply k10ModelCoverCheck_split_true
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
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
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
                                · decide +kernel
                              · decide +kernel
                            · decide +kernel
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
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
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
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                          · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · decide +kernel
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
                        · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · decide +kernel
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
                      · apply k10ModelCoverCheck_split_true
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
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                          · apply k10ModelCoverCheck_split_true
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
                                · decide +kernel
                              · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · apply k10ModelCoverCheck_split_true
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
                                    · apply k10ModelCoverCheck_split_true
                                      · decide +kernel
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
                                    · decide +kernel
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
                            · decide +kernel
                            · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
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
                          · decide +kernel
                          · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · apply k10ModelCoverCheck_split_true
                                  · decide +kernel
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
                          · apply k10ModelCoverCheck_split_true
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
                                    · decide +kernel
                                  · apply k10ModelCoverCheck_split_true
                                    · decide +kernel
                                    · decide +kernel
                                · apply k10ModelCoverCheck_split_true
                                  · apply k10ModelCoverCheck_split_true
                                    · decide +kernel
                                    · decide +kernel
                                  · decide +kernel
                              · decide +kernel
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
                                · decide +kernel
                              · decide +kernel
                            · decide +kernel
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
                            · apply k10ModelCoverCheck_split_true
                              · decide +kernel
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
                      · apply k10ModelCoverCheck_split_true
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
                      · decide +kernel
                    · apply k10ModelCoverCheck_split_true
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
                          · decide +kernel
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
                            · decide +kernel
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
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
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
                  · decide +kernel
                  · decide +kernel
                · apply k10ModelCoverCheck_split_true
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
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
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
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
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
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
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
                          · decide +kernel
                        · decide +kernel
                      · apply k10ModelCoverCheck_split_true
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
                              · decide +kernel
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
                          · decide +kernel
                          · decide +kernel
                        · decide +kernel
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
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
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
              · apply k10ModelCoverCheck_split_true
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
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
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                        · decide +kernel
                      · decide +kernel
                    · decide +kernel
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
                  · decide +kernel
                · decide +kernel
              · apply k10ModelCoverCheck_split_true
                · apply k10ModelCoverCheck_split_true
                  · decide +kernel
                  · decide +kernel
                · decide +kernel
            · apply k10ModelCoverCheck_split_true
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
                            · decide +kernel
                            · decide +kernel
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
                        · decide +kernel
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
                · apply k10ModelCoverCheck_split_true
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
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
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
                            · decide +kernel
                            · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
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
              · apply k10ModelCoverCheck_split_true
                · apply k10ModelCoverCheck_split_true
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
            · apply k10ModelCoverCheck_split_true
              · apply k10ModelCoverCheck_split_true
                · apply k10ModelCoverCheck_split_true
                  · decide +kernel
                  · decide +kernel
                · apply k10ModelCoverCheck_split_true
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
                · decide +kernel
                · decide +kernel
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
              · apply k10ModelCoverCheck_split_true
                · decide +kernel
                · decide +kernel
              · decide +kernel
            · decide +kernel
          · decide +kernel
        · decide +kernel
      · decide +kernel


def k10p15chunk34Box : Certificate.ClosedBox 5 := ⟨![(1341 / 800), (1341 / 800), (1341 / 800), (1341 / 800), (1341 / 800)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk34Tree : K10ModelCover := (.split 0 (2733 / 1600) k10p15chunk32Tree k10p15chunk33Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk34Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk34Box k10p15chunk34Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk34Box.left 0 (2733 / 1600)) = k10p15chunk32Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk34Box k10p15chunk32Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk32Checked
  · have heq : k10CachedBox (k10p15chunk34Box.right 0 (2733 / 1600)) = k10p15chunk33Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk34Box k10p15chunk33Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk33Checked


def k10p15chunk35Box : Certificate.ClosedBox 5 := ⟨![(1341 / 800), (1341 / 800), (1341 / 800), (1341 / 800), (129 / 80)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk35Tree : K10ModelCover := (.split 4 (1341 / 800) k10p15chunk29Tree k10p15chunk34Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk35Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk35Box k10p15chunk35Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk35Box.left 4 (1341 / 800)) = k10p15chunk29Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk35Box k10p15chunk29Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk29Checked
  · have heq : k10CachedBox (k10p15chunk35Box.right 4 (1341 / 800)) = k10p15chunk34Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk35Box k10p15chunk34Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk34Checked


def k10p15chunk36Box : Certificate.ClosedBox 5 := ⟨![(1341 / 800), (1341 / 800), (1341 / 800), (129 / 80), (129 / 80)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk36Tree : K10ModelCover := (.split 3 (1341 / 800) k10p15chunk28Tree k10p15chunk35Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk36Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk36Box k10p15chunk36Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk36Box.left 3 (1341 / 800)) = k10p15chunk28Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk36Box k10p15chunk28Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk28Checked
  · have heq : k10CachedBox (k10p15chunk36Box.right 3 (1341 / 800)) = k10p15chunk35Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk36Box k10p15chunk35Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk35Checked


def k10p15chunk37Box : Certificate.ClosedBox 5 := ⟨![(1341 / 800), (1341 / 800), (129 / 80), (129 / 80), (129 / 80)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk37Tree : K10ModelCover := (.split 2 (1341 / 800) k10p15chunk27Tree k10p15chunk36Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk37Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk37Box k10p15chunk37Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk37Box.left 2 (1341 / 800)) = k10p15chunk27Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk37Box k10p15chunk27Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk27Checked
  · have heq : k10CachedBox (k10p15chunk37Box.right 2 (1341 / 800)) = k10p15chunk36Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk37Box k10p15chunk36Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk36Checked


def k10p15chunk38Box : Certificate.ClosedBox 5 := ⟨![(1341 / 800), (129 / 80), (129 / 80), (129 / 80), (129 / 80)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk38Tree : K10ModelCover := (.split 1 (1341 / 800) k10p15chunk26Tree k10p15chunk37Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk38Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk38Box k10p15chunk38Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk38Box.left 1 (1341 / 800)) = k10p15chunk26Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk38Box k10p15chunk26Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk26Checked
  · have heq : k10CachedBox (k10p15chunk38Box.right 1 (1341 / 800)) = k10p15chunk37Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk38Box k10p15chunk37Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk37Checked


def k10p15chunk39Box : Certificate.ClosedBox 5 := ⟨![(129 / 80), (129 / 80), (129 / 80), (129 / 80), (129 / 80)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk39Tree : K10ModelCover := (.split 0 (1341 / 800) k10p15chunk25Tree k10p15chunk38Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk39Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk39Box k10p15chunk39Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk39Box.left 0 (1341 / 800)) = k10p15chunk25Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk39Box k10p15chunk25Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk25Checked
  · have heq : k10CachedBox (k10p15chunk39Box.right 0 (1341 / 800)) = k10p15chunk38Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk39Box k10p15chunk38Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk38Checked


def k10p15chunk40Box : Certificate.ClosedBox 5 := ⟨![(129 / 80), (129 / 80), (129 / 80), (129 / 80), (297 / 200)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk40Tree : K10ModelCover := (.split 4 (129 / 80) k10p15chunk24Tree k10p15chunk39Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk40Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk40Box k10p15chunk40Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk40Box.left 4 (129 / 80)) = k10p15chunk24Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk40Box k10p15chunk24Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk24Checked
  · have heq : k10CachedBox (k10p15chunk40Box.right 4 (129 / 80)) = k10p15chunk39Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk40Box k10p15chunk39Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk39Checked


def k10p15chunk41Box : Certificate.ClosedBox 5 := ⟨![(129 / 80), (129 / 80), (129 / 80), (297 / 200), (297 / 200)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk41Tree : K10ModelCover := (.split 3 (129 / 80) k10p15chunk23Tree k10p15chunk40Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk41Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk41Box k10p15chunk41Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk41Box.left 3 (129 / 80)) = k10p15chunk23Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk41Box k10p15chunk23Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk23Checked
  · have heq : k10CachedBox (k10p15chunk41Box.right 3 (129 / 80)) = k10p15chunk40Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk41Box k10p15chunk40Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk40Checked


def k10p15chunk42Box : Certificate.ClosedBox 5 := ⟨![(129 / 80), (129 / 80), (297 / 200), (297 / 200), (297 / 200)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk42Tree : K10ModelCover := (.split 2 (129 / 80) k10p15chunk22Tree k10p15chunk41Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk42Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk42Box k10p15chunk42Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk42Box.left 2 (129 / 80)) = k10p15chunk22Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk42Box k10p15chunk22Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk22Checked
  · have heq : k10CachedBox (k10p15chunk42Box.right 2 (129 / 80)) = k10p15chunk41Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk42Box k10p15chunk41Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk41Checked


def k10p15chunk43Box : Certificate.ClosedBox 5 := ⟨![(129 / 80), (297 / 200), (297 / 200), (297 / 200), (297 / 200)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk43Tree : K10ModelCover := (.split 1 (129 / 80) k10p15chunk21Tree k10p15chunk42Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk43Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk43Box k10p15chunk43Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk43Box.left 1 (129 / 80)) = k10p15chunk21Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk43Box k10p15chunk21Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk21Checked
  · have heq : k10CachedBox (k10p15chunk43Box.right 1 (129 / 80)) = k10p15chunk42Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk43Box k10p15chunk42Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk42Checked


def k10p15chunk44Box : Certificate.ClosedBox 5 := ⟨![(297 / 200), (297 / 200), (297 / 200), (297 / 200), (297 / 200)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk44Tree : K10ModelCover := (.split 0 (129 / 80) k10p15chunk20Tree k10p15chunk43Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk44Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk44Box k10p15chunk44Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk44Box.left 0 (129 / 80)) = k10p15chunk20Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk44Box k10p15chunk20Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk20Checked
  · have heq : k10CachedBox (k10p15chunk44Box.right 0 (129 / 80)) = k10p15chunk43Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk44Box k10p15chunk43Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk43Checked


def k10p15chunk45Box : Certificate.ClosedBox 5 := ⟨![(297 / 200), (297 / 200), (297 / 200), (297 / 200), (123 / 100)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk45Tree : K10ModelCover := (.split 4 (297 / 200) k10p15chunk19Tree k10p15chunk44Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk45Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk45Box k10p15chunk45Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk45Box.left 4 (297 / 200)) = k10p15chunk19Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk45Box k10p15chunk19Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk19Checked
  · have heq : k10CachedBox (k10p15chunk45Box.right 4 (297 / 200)) = k10p15chunk44Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk45Box k10p15chunk44Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk44Checked


def k10p15chunk46Box : Certificate.ClosedBox 5 := ⟨![(297 / 200), (297 / 200), (297 / 200), (123 / 100), (123 / 100)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk46Tree : K10ModelCover := (.split 3 (297 / 200) k10p15chunk18Tree k10p15chunk45Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk46Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk46Box k10p15chunk46Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk46Box.left 3 (297 / 200)) = k10p15chunk18Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk46Box k10p15chunk18Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk18Checked
  · have heq : k10CachedBox (k10p15chunk46Box.right 3 (297 / 200)) = k10p15chunk45Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk46Box k10p15chunk45Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk45Checked


def k10p15chunk47Box : Certificate.ClosedBox 5 := ⟨![(297 / 200), (297 / 200), (123 / 100), (123 / 100), (123 / 100)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk47Tree : K10ModelCover := (.split 2 (297 / 200) k10p15chunk17Tree k10p15chunk46Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk47Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk47Box k10p15chunk47Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk47Box.left 2 (297 / 200)) = k10p15chunk17Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk47Box k10p15chunk17Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk17Checked
  · have heq : k10CachedBox (k10p15chunk47Box.right 2 (297 / 200)) = k10p15chunk46Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk47Box k10p15chunk46Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk46Checked


def k10p15chunk48Box : Certificate.ClosedBox 5 := ⟨![(297 / 200), (123 / 100), (123 / 100), (123 / 100), (123 / 100)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk48Tree : K10ModelCover := (.split 1 (297 / 200) k10p15chunk16Tree k10p15chunk47Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk48Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk48Box k10p15chunk48Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk48Box.left 1 (297 / 200)) = k10p15chunk16Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk48Box k10p15chunk16Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk16Checked
  · have heq : k10CachedBox (k10p15chunk48Box.right 1 (297 / 200)) = k10p15chunk47Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk48Box k10p15chunk47Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk47Checked


def k10p15chunk49Box : Certificate.ClosedBox 5 := ⟨![(123 / 100), (123 / 100), (123 / 100), (123 / 100), (123 / 100)], ![(87 / 50), (87 / 50), (87 / 50), (87 / 50), (87 / 50)]⟩
def k10p15chunk49Tree : K10ModelCover := (.split 0 (297 / 200) k10p15chunk15Tree k10p15chunk48Tree)

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk49Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk49Box k10p15chunk49Tree = true := by
  apply k10ModelCoverCheck_split_true
  · have heq : k10CachedBox (k10p15chunk49Box.left 0 (297 / 200)) = k10p15chunk15Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk49Box k10p15chunk15Box Certificate.ClosedBox.left
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk15Checked
  · have heq : k10CachedBox (k10p15chunk49Box.right 0 (297 / 200)) = k10p15chunk48Box := by
      rw [k10CachedBox_eq]
      unfold k10p15chunk49Box k10p15chunk48Box Certificate.ClosedBox.right
      congr 1 <;> funext j <;> fin_cases j <;> norm_num [Function.update]
    rw [heq]
    exact k10p15chunk48Checked


def k10p15chunk50Box : Certificate.ClosedBox 5 := ⟨![(123 / 100), (123 / 100), (123 / 100), (123 / 100), (87 / 50)], ![(297 / 200), (87 / 50), (87 / 50), (87 / 50), (9 / 4)]⟩
def k10p15chunk50Tree : K10ModelCover := (.split 1 (297 / 200) (.split 2 (297 / 200) (.inner ![303, 303, 152, 304, 305]) (.split 3 (297 / 200) (.split 4 (399 / 200) (.inner ![303, 152, 152, 306, 306]) (.split 0 (543 / 400) (.inner ![307, 152, 152, 305, 308]) (.split 1 (543 / 400) (.inner ![307, 309, 152, 305, 305]) (.split 2 (129 / 80) (.inner ![303, 310, 310, 305, 305]) (.cycle 4 [(.support 4 0 49 5), (.pair 0 1 303), (.pair 1 2 152), (.support 2 4 31 49)]))))) (.split 4 (399 / 200) (.inner ![303, 152, 1, 311, 306]) (.split 0 (543 / 400) (.split 1 (543 / 400) (.inner ![21, 309, 1, 304, 308]) (.split 2 (129 / 80) (.inner ![307, 310, 154, 304, 308]) (.cycle 4 [(.pair 4 0 308), (.pair 0 1 307), (.pair 1 2 152), (.support 2 4 31 49)]))) (.split 1 (543 / 400) (.cycle 0 [(.pair 0 1 307), (.pair 1 2 309), (.pair 2 3 1), (.support 3 4 2 49), (.support 4 0 49 5)]) (.split 2 (129 / 80) (.cycle 0 [(.pair 0 1 303), (.pair 1 2 310), (.pair 2 3 154), (.support 3 4 2 49), (.support 4 0 49 5)]) (.cycle 4 [(.support 4 0 49 5), (.pair 0 1 303), (.pair 1 2 152), (.support 2 4 31 49)]))))))) (.split 2 (297 / 200) (.split 3 (297 / 200) (.split 4 (399 / 200) (.inner ![152, 152, 303, 306, 306]) (.split 0 (543 / 400) (.inner ![309, 152, 303, 305, 308]) (.split 1 (129 / 80) (.inner ![310, 310, 303, 305, 305]) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 152), (.pair 2 3 303), (.support 3 4 0 49)])))) (.split 4 (399 / 200) (.inner ![152, 152, 152, 311, 306]) (.split 0 (543 / 400) (.split 1 (129 / 80) (.inner ![313, 310, 152, 304, 308]) (.split 2 (543 / 400) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 309), (.pair 2 3 309), (.support 3 4 2 49)]) (.split 3 (129 / 80) (.split 4 (849 / 400) (.inner ![309, 152, 310, 314, 315]) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 152), (.pair 2 3 310), (.support 3 4 2 50)])) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 152), (.pair 2 3 152), (.support 3 4 31 49)])))) (.split 1 (129 / 80) (.split 2 (543 / 400) (.inner ![310, 313, 309, 304, 305]) (.split 3 (129 / 80) (.inner ![310, 310, 310, 312, 305]) (.cycle 0 [(.pair 0 1 310), (.pair 1 2 310), (.pair 2 3 152), (.support 3 4 31 49), (.support 4 0 49 5)]))) (.split 2 (543 / 400) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 309), (.pair 2 3 309), (.support 3 4 2 49)]) (.split 3 (129 / 80) (.split 4 (849 / 400) (.inner ![152, 152, 310, 314, 316]) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 152), (.pair 2 3 310), (.support 3 4 2 50)])) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 152), (.pair 2 3 152), (.support 3 4 31 49)]))))))) (.split 3 (297 / 200) (.split 4 (399 / 200) (.split 0 (543 / 400) (.inner ![309, 1, 152, 306, 317]) (.split 1 (129 / 80) (.inner ![310, 154, 152, 306, 306]) (.split 2 (129 / 80) (.inner ![152, 154, 310, 306, 306]) (.split 3 (543 / 400) (.inner ![152, 1, 309, 317, 306]) (.split 4 (747 / 400) (.inner ![152, 1, 152, 318, 318]) (.split 0 (1137 / 800) (.inner ![319, 1, 152, 306, 320]) (.split 1 (1341 / 800) (.inner ![321, 156, 152, 306, 306]) (.split 2 (1341 / 800) (.inner ![152, 156, 321, 306, 306]) (.split 3 (1137 / 800) (.inner ![152, 1, 319, 320, 306]) (.split 4 (309 / 160) (.inner ![152, 1, 152, 322, 322]) (.split 0 (93 / 64) (.inner ![323, 1, 152, 306, 324]) (.split 1 (2733 / 1600) (.inner ![325, 160, 152, 306, 306]) (.outer ![16, 27, 28, 7, 51]))))))))))))) (.split 0 (543 / 400) (.split 1 (129 / 80) (.split 2 (129 / 80) (.inner ![313, 153, 310, 305, 308]) (.cycle 4 [(.pair 4 0 308), (.pair 0 1 313), (.pair 1 2 154), (.support 2 4 31 49)])) (.split 2 (129 / 80) (.split 3 (543 / 400) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 154), (.pair 2 3 313), (.pair 3 4 308)]) (.split 4 (849 / 400) (.inner ![309, 154, 310, 316, 315]) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 154), (.pair 2 3 310), (.support 3 4 5 50)]))) (.split 3 (543 / 400) (.split 4 (849 / 400) (.inner ![309, 1, 309, 315, 315]) (.split 0 (207 / 160) (.split 1 (1341 / 800) (.cycle 4 [(.support 4 0 50 0), (.pair 0 1 326), (.pair 1 2 156), (.support 2 4 31 50)]) (.outer ![0, 28, 31, 0, 50])) (.split 1 (1341 / 800) (.cycle 4 [(.support 4 0 50 12), (.pair 0 1 329), (.pair 1 2 156), (.support 2 4 31 50)]) (.outer ![12, 28, 31, 0, 50])))) (.split 4 (849 / 400) (.split 0 (207 / 160) (.split 1 (1341 / 800) (.inner ![326, 156, 152, 316, 330]) (.split 2 (1341 / 800) (.inner ![327, 156, 321, 316, 330]) (.outer ![0, 28, 28, 5, 49]))) (.split 1 (1341 / 800) (.inner ![329, 156, 152, 316, 315]) (.split 2 (1341 / 800) (.split 3 (1137 / 800) (.inner ![309, 156, 331, 332, 315]) (.split 4 (1647 / 800) (.inner ![309, 156, 321, 333, 334]) (.cycle 4 [(.support 4 1 52 28), (.pair 1 2 156), (.pair 2 3 321), (.pair 3 4 316)]))) (.outer ![12, 28, 28, 5, 49])))) (.split 0 (207 / 160) (.split 1 (1341 / 800) (.cycle 4 [(.support 4 0 50 0), (.pair 0 1 326), (.pair 1 2 156), (.support 2 4 31 50)]) (.outer ![0, 28, 31, 5, 50])) (.split 1 (1341 / 800) (.cycle 4 [(.support 4 0 50 12), (.pair 0 1 329), (.pair 1 2 156), (.support 2 4 31 50)]) (.outer ![12, 28, 31, 5, 50]))))))) (.split 1 (129 / 80) (.split 2 (129 / 80) (.split 3 (543 / 400) (.inner ![310, 153, 313, 308, 305]) (.split 4 (849 / 400) (.inner ![310, 153, 310, 316, 316]) (.cycle 0 [(.pair 0 1 310), (.pair 1 2 153), (.pair 2 3 310), (.support 3 4 5 50), (.support 4 0 50 5)]))) (.split 3 (543 / 400) (.split 4 (849 / 400) (.inner ![310, 154, 309, 315, 316]) (.cycle 4 [(.support 4 0 50 5), (.pair 0 1 310), (.pair 1 2 154), (.support 2 4 31 50)])) (.split 4 (849 / 400) (.split 0 (1137 / 800) (.inner ![337, 154, 152, 316, 332]) (.split 1 (1239 / 800) (.inner ![338, 157, 152, 316, 316]) (.split 2 (1341 / 800) (.inner ![310, 161, 321, 316, 316]) (.cycle 4 [(.pair 4 0 316), (.pair 0 1 310), (.pair 1 2 154), (.support 2 4 28 49)])))) (.cycle 4 [(.support 4 0 50 5), (.pair 0 1 310), (.pair 1 2 154), (.support 2 4 31 50)])))) (.split 2 (129 / 80) (.split 3 (543 / 400) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 154), (.pair 2 3 313), (.pair 3 4 308)]) (.split 4 (849 / 400) (.split 0 (1137 / 800) (.inner ![319, 154, 310, 316, 332]) (.split 1 (1341 / 800) (.inner ![321, 161, 310, 316, 316]) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 154), (.pair 2 3 310), (.pair 3 4 316)]))) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 154), (.pair 2 3 310), (.support 3 4 5 50)]))) (.split 3 (543 / 400) (.split 4 (849 / 400) (.split 0 (1137 / 800) (.split 1 (1341 / 800) (.inner ![331, 156, 309, 315, 332]) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 1), (.pair 2 3 309), (.pair 3 4 315)])) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.inner ![321, 162, 329, 315, 316]) (.split 3 (207 / 160) (.inner ![321, 156, 327, 330, 316]) (.split 4 (1647 / 800) (.inner ![321, 156, 309, 334, 333]) (.cycle 2 [(.support 2 4 28 52), (.support 4 1 52 31), (.pair 1 2 156)])))) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 1), (.pair 2 3 309), (.pair 3 4 315)]))) (.split 0 (1137 / 800) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 162), (.pair 2 3 329), (.support 3 4 0 50)]) (.outer ![5, 31, 28, 0, 50])) (.outer ![5, 28, 31, 0, 50])) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 162), (.pair 2 3 329), (.support 3 4 0 50)]) (.outer ![7, 31, 28, 0, 50])) (.outer ![7, 28, 31, 0, 50])))) (.split 4 (849 / 400) (.split 0 (1137 / 800) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.inner ![331, 162, 321, 316, 332]) (.cycle 4 [(.pair 4 0 332), (.pair 0 1 331), (.pair 1 2 156), (.support 2 4 28 49)])) (.split 2 (1341 / 800) (.split 3 (1137 / 800) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 156), (.pair 2 3 331), (.pair 3 4 332)]) (.split 4 (1647 / 800) (.inner ![319, 156, 321, 333, 342]) (.cycle 4 [(.support 4 1 52 28), (.pair 1 2 156), (.pair 2 3 321), (.pair 3 4 316)]))) (.outer ![5, 28, 28, 5, 49]))) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.split 3 (1137 / 800) (.inner ![321, 162, 331, 332, 316]) (.split 4 (1647 / 800) (.inner ![321, 162, 321, 333, 333]) (.split 0 (93 / 64) (.inner ![343, 162, 321, 316, 344]) (.split 1 (2631 / 1600) (.inner ![345, 171, 321, 316, 316]) (.cycle 4 [(.support 4 1 52 30), (.pair 1 2 162), (.pair 2 3 321), (.pair 3 4 316)]))))) (.split 3 (1137 / 800) (.split 4 (1647 / 800) (.inner ![321, 156, 319, 342, 333]) (.cycle 2 [(.support 2 4 28 52), (.support 4 1 52 31), (.pair 1 2 156)])) (.split 4 (1647 / 800) (.cycle 4 [(.pair 4 0 333), (.pair 0 1 321), (.pair 1 2 156), (.support 2 4 28 49)]) (.cycle 2 [(.support 2 4 28 52), (.support 4 1 52 31), (.pair 1 2 156)])))) (.split 2 (1341 / 800) (.split 3 (1137 / 800) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 156), (.pair 2 3 331), (.pair 3 4 332)]) (.split 4 (1647 / 800) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 156), (.pair 2 3 321), (.pair 3 4 333)]) (.cycle 4 [(.support 4 1 52 28), (.pair 1 2 156), (.pair 2 3 321), (.pair 3 4 316)]))) (.outer ![7, 28, 28, 5, 49])))) (.split 0 (1137 / 800) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.cycle 2 [(.support 2 4 31 50), (.support 4 1 50 31), (.pair 1 2 162)]) (.outer ![5, 31, 28, 5, 50])) (.outer ![5, 28, 31, 5, 50])) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.cycle 2 [(.support 2 4 31 50), (.support 4 1 50 31), (.pair 1 2 162)]) (.outer ![7, 31, 28, 5, 50])) (.outer ![7, 28, 31, 5, 50]))))))))) (.split 4 (399 / 200) (.split 0 (543 / 400) (.split 1 (129 / 80) (.inner ![313, 154, 1, 311, 317]) (.split 2 (129 / 80) (.inner ![309, 154, 154, 311, 317]) (.split 3 (129 / 80) (.split 4 (747 / 400) (.inner ![309, 1, 154, 133, 151]) (.split 0 (207 / 160) (.inner ![327, 1, 154, 348, 349]) (.split 1 (1341 / 800) (.inner ![329, 156, 154, 348, 317]) (.split 2 (1341 / 800) (.inner ![309, 156, 161, 348, 317]) (.cycle 4 [(.pair 4 0 317), (.pair 0 1 309), (.pair 1 2 1), (.support 2 4 28 53)]))))) (.split 4 (747 / 400) (.inner ![309, 1, 1, 134, 151]) (.cycle 0 [(.pair 0 1 309), (.pair 1 2 1), (.pair 2 3 1), (.support 3 4 31 53), (.pair 4 0 317)]))))) (.split 1 (129 / 80) (.split 2 (129 / 80) (.inner ![310, 153, 154, 311, 306]) (.split 3 (129 / 80) (.inner ![310, 154, 154, 348, 306]) (.cycle 0 [(.pair 0 1 310), (.pair 1 2 154), (.pair 2 3 1), (.support 3 4 31 54), (.pair 4 0 306)]))) (.split 2 (129 / 80) (.split 3 (129 / 80) (.inner ![152, 154, 153, 348, 306]) (.split 4 (747 / 400) (.inner ![152, 154, 154, 134, 318]) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 154), (.pair 2 3 154), (.support 3 4 31 53), (.pair 4 0 306)]))) (.split 3 (129 / 80) (.split 4 (747 / 400) (.inner ![152, 1, 154, 133, 318]) (.split 0 (1137 / 800) (.split 1 (1341 / 800) (.inner ![331, 156, 154, 348, 320]) (.split 2 (1341 / 800) (.split 3 (1239 / 800) (.inner ![319, 156, 155, 350, 320]) (.cycle 0 [(.pair 0 1 319), (.pair 1 2 156), (.pair 2 3 161), (.support 3 4 32 53), (.pair 4 0 320)])) (.split 3 (1239 / 800) (.split 4 (309 / 160) (.inner ![319, 1, 157, 352, 353]) (.cycle 4 [(.pair 4 0 320), (.pair 0 1 319), (.pair 1 2 1), (.support 2 4 28 51)])) (.split 4 (309 / 160) (.inner ![319, 1, 154, 355, 353]) (.cycle 4 [(.pair 4 0 320), (.pair 0 1 319), (.pair 1 2 1), (.support 2 4 28 51)]))))) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.inner ![321, 162, 161, 348, 306]) (.cycle 4 [(.pair 4 0 306), (.pair 0 1 321), (.pair 1 2 156), (.support 2 4 28 53)])) (.split 2 (1341 / 800) (.split 3 (1239 / 800) (.inner ![152, 156, 155, 350, 306]) (.split 4 (309 / 160) (.inner ![152, 156, 161, 355, 322]) (.split 0 (93 / 64) (.cycle 0 [(.pair 0 1 323), (.pair 1 2 156), (.pair 2 3 161), (.support 3 4 32 51), (.pair 4 0 324)]) (.split 1 (2733 / 1600) (.cycle 0 [(.pair 0 1 325), (.pair 1 2 167), (.pair 2 3 161), (.support 3 4 32 51), (.pair 4 0 306)]) (.cycle 4 [(.support 4 1 51 27), (.pair 1 2 156), (.pair 2 3 161), (.support 3 4 32 51)]))))) (.split 3 (1239 / 800) (.split 4 (309 / 160) (.inner ![152, 1, 157, 352, 322]) (.split 0 (93 / 64) (.cycle 4 [(.pair 4 0 324), (.pair 0 1 323), (.pair 1 2 1), (.support 2 4 28 51)]) (.split 1 (2733 / 1600) (.cycle 4 [(.pair 4 0 306), (.pair 0 1 325), (.pair 1 2 160), (.support 2 4 28 51)]) (.outer ![16, 27, 28, 2, 51])))) (.split 4 (309 / 160) (.split 0 (93 / 64) (.cycle 4 [(.pair 4 0 358), (.pair 0 1 323), (.pair 1 2 1), (.support 2 4 28 53)]) (.split 1 (2733 / 1600) (.cycle 4 [(.pair 4 0 322), (.pair 0 1 325), (.pair 1 2 160), (.support 2 4 28 53)]) (.cycle 4 [(.pair 4 0 322), (.pair 0 1 152), (.support 1 2 27 28), (.support 2 4 28 53)]))) (.split 0 (93 / 64) (.cycle 4 [(.pair 4 0 324), (.pair 0 1 323), (.pair 1 2 1), (.support 2 4 28 51)]) (.split 1 (2733 / 1600) (.cycle 4 [(.pair 4 0 306), (.pair 0 1 325), (.pair 1 2 160), (.support 2 4 28 51)]) (.outer ![16, 27, 28, 32, 51]))))))))) (.split 4 (747 / 400) (.split 0 (1137 / 800) (.cycle 0 [(.pair 0 1 319), (.pair 1 2 1), (.pair 2 3 1), (.support 3 4 31 54), (.pair 4 0 361)]) (.split 1 (1341 / 800) (.cycle 0 [(.pair 0 1 321), (.pair 1 2 156), (.pair 2 3 1), (.support 3 4 31 54), (.pair 4 0 318)]) (.split 2 (1341 / 800) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 156), (.pair 2 3 156), (.support 3 4 31 54), (.pair 4 0 318)]) (.split 3 (1341 / 800) (.split 4 (1443 / 800) (.inner ![152, 1, 156, 363, 364]) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 1), (.pair 2 3 156), (.support 3 4 31 55), (.pair 4 0 318)])) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 1), (.pair 2 3 1), (.support 3 4 28 54), (.pair 4 0 318)]))))) (.split 0 (1137 / 800) (.cycle 0 [(.pair 0 1 319), (.pair 1 2 1), (.pair 2 3 1), (.support 3 4 31 53), (.pair 4 0 320)]) (.split 1 (1341 / 800) (.cycle 0 [(.pair 0 1 321), (.pair 1 2 156), (.pair 2 3 1), (.support 3 4 31 53), (.pair 4 0 306)]) (.split 2 (1341 / 800) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 156), (.pair 2 3 156), (.support 3 4 31 53), (.pair 4 0 306)]) (.split 3 (1341 / 800) (.split 4 (309 / 160) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 1), (.pair 2 3 156), (.support 3 4 31 53), (.pair 4 0 322)]) (.cycle 4 [(.support 4 1 51 28), (.pair 1 2 1), (.pair 2 3 156), (.support 3 4 31 51)])) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 1), (.pair 2 3 1), (.support 3 4 28 53), (.pair 4 0 306)])))))))))) (.split 0 (543 / 400) (.split 1 (129 / 80) (.split 2 (129 / 80) (.split 3 (129 / 80) (.cycle 0 [(.pair 0 1 313), (.pair 1 2 153), (.pair 2 3 153), (.support 3 4 2 49), (.pair 4 0 308)]) (.cycle 0 [(.pair 0 1 313), (.pair 1 2 153), (.pair 2 3 154), (.support 3 4 31 49), (.pair 4 0 308)])) (.cycle 4 [(.pair 4 0 308), (.pair 0 1 313), (.pair 1 2 154), (.support 2 4 31 49)])) (.split 2 (129 / 80) (.split 3 (129 / 80) (.split 4 (849 / 400) (.split 0 (207 / 160) (.inner ![327, 154, 153, 314, 330]) (.split 1 (1341 / 800) (.inner ![329, 161, 153, 314, 315]) (.split 2 (1239 / 800) (.inner ![309, 157, 366, 314, 315]) (.split 3 (1239 / 800) (.inner ![309, 154, 366, 367, 315]) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 154), (.pair 2 3 153), (.support 3 4 32 49)]))))) (.split 0 (207 / 160) (.split 1 (1341 / 800) (.cycle 0 [(.pair 0 1 326), (.pair 1 2 161), (.pair 2 3 153), (.support 3 4 2 50), (.support 4 0 50 0)]) (.outer ![0, 28, 2, 2, 50])) (.split 1 (1341 / 800) (.split 2 (1239 / 800) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 155), (.pair 2 3 366), (.support 3 4 2 50)]) (.split 3 (1239 / 800) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 161), (.pair 2 3 366), (.support 3 4 2 50)]) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 161), (.pair 2 3 153), (.support 3 4 32 50)]))) (.outer ![12, 28, 2, 2, 50])))) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 154), (.pair 2 3 154), (.support 3 4 31 49)])) (.split 3 (129 / 80) (.split 4 (849 / 400) (.split 0 (207 / 160) (.split 1 (1341 / 800) (.cycle 4 [(.pair 4 0 330), (.pair 0 1 326), (.pair 1 2 156), (.support 2 4 31 49)]) (.split 2 (1341 / 800) (.cycle 4 [(.pair 4 0 330), (.pair 0 1 327), (.pair 1 2 156), (.support 2 4 31 49)]) (.outer ![0, 28, 28, 2, 49]))) (.split 1 (1341 / 800) (.cycle 4 [(.pair 4 0 315), (.pair 0 1 329), (.pair 1 2 156), (.support 2 4 31 49)]) (.split 2 (1341 / 800) (.split 3 (1239 / 800) (.split 4 (1647 / 800) (.inner ![309, 156, 155, 371, 334]) (.cycle 2 [(.support 2 4 31 52), (.support 4 1 52 28), (.pair 1 2 156)])) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 156), (.pair 2 3 161), (.support 3 4 32 49)])) (.outer ![12, 28, 28, 2, 49])))) (.split 0 (207 / 160) (.split 1 (1341 / 800) (.cycle 4 [(.support 4 0 50 0), (.pair 0 1 326), (.pair 1 2 156), (.support 2 4 31 50)]) (.outer ![0, 28, 31, 2, 50])) (.split 1 (1341 / 800) (.cycle 4 [(.support 4 0 50 12), (.pair 0 1 329), (.pair 1 2 156), (.support 2 4 31 50)]) (.outer ![12, 28, 31, 2, 50])))) (.split 4 (849 / 400) (.cycle 0 [(.pair 0 1 309), (.pair 1 2 1), (.pair 2 3 1), (.support 3 4 31 49), (.pair 4 0 315)]) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 1), (.pair 2 3 1), (.support 3 4 31 50)]))))) (.split 1 (129 / 80) (.split 2 (129 / 80) (.split 3 (129 / 80) (.split 4 (849 / 400) (.inner ![310, 153, 153, 314, 316]) (.cycle 0 [(.pair 0 1 310), (.pair 1 2 153), (.pair 2 3 153), (.support 3 4 2 50), (.support 4 0 50 5)])) (.cycle 0 [(.pair 0 1 310), (.pair 1 2 153), (.pair 2 3 154), (.support 3 4 31 49), (.support 4 0 49 5)])) (.split 3 (129 / 80) (.split 4 (849 / 400) (.split 0 (1137 / 800) (.cycle 4 [(.pair 4 0 332), (.pair 0 1 337), (.pair 1 2 154), (.support 2 4 31 49)]) (.split 1 (1239 / 800) (.cycle 4 [(.pair 4 0 316), (.pair 0 1 338), (.pair 1 2 157), (.support 2 4 31 49)]) (.split 2 (1341 / 800) (.cycle 4 [(.pair 4 0 316), (.pair 0 1 310), (.pair 1 2 161), (.support 2 4 31 49)]) (.cycle 4 [(.pair 4 0 316), (.pair 0 1 310), (.pair 1 2 154), (.support 2 4 28 49)])))) (.cycle 4 [(.support 4 0 50 5), (.pair 0 1 310), (.pair 1 2 154), (.support 2 4 31 50)])) (.cycle 0 [(.pair 0 1 310), (.pair 1 2 154), (.pair 2 3 1), (.support 3 4 31 49), (.support 4 0 49 5)]))) (.split 2 (129 / 80) (.split 3 (129 / 80) (.split 4 (849 / 400) (.split 0 (1137 / 800) (.split 1 (1341 / 800) (.split 2 (1239 / 800) (.inner ![331, 155, 366, 314, 332]) (.split 3 (1239 / 800) (.inner ![331, 161, 366, 367, 332]) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 161), (.pair 2 3 153), (.support 3 4 32 49)]))) (.split 2 (1239 / 800) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 157), (.pair 2 3 366), (.pair 3 4 314)]) (.split 3 (1239 / 800) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 154), (.pair 2 3 366), (.pair 3 4 367)]) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 154), (.pair 2 3 153), (.support 3 4 32 49)])))) (.split 1 (1341 / 800) (.split 2 (1239 / 800) (.inner ![321, 155, 366, 314, 316]) (.split 3 (1239 / 800) (.split 4 (1647 / 800) (.inner ![321, 161, 366, 371, 333]) (.split 0 (93 / 64) (.inner ![343, 161, 366, 367, 344]) (.split 1 (2631 / 1600) (.inner ![345, 165, 366, 367, 316]) (.cycle 4 [(.support 4 1 52 30), (.pair 1 2 161), (.pair 2 3 366), (.pair 3 4 367)])))) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 161), (.pair 2 3 153), (.support 3 4 32 49)]))) (.split 2 (1239 / 800) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 157), (.pair 2 3 366), (.pair 3 4 314)]) (.split 3 (1239 / 800) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 154), (.pair 2 3 366), (.pair 3 4 367)]) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 154), (.pair 2 3 153), (.support 3 4 32 49)]))))) (.split 0 (1137 / 800) (.split 1 (1341 / 800) (.split 2 (1239 / 800) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 155), (.pair 2 3 366), (.support 3 4 2 50)]) (.split 3 (1239 / 800) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 161), (.pair 2 3 366), (.support 3 4 2 50)]) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 161), (.pair 2 3 153), (.support 3 4 32 50)]))) (.outer ![5, 28, 2, 2, 50])) (.split 1 (1341 / 800) (.split 2 (1239 / 800) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 155), (.pair 2 3 366), (.support 3 4 2 50)]) (.split 3 (1239 / 800) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 161), (.pair 2 3 366), (.support 3 4 2 50)]) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 161), (.pair 2 3 153), (.support 3 4 32 50)]))) (.outer ![7, 28, 2, 2, 50])))) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 154), (.pair 2 3 154), (.support 3 4 31 49)])) (.split 3 (129 / 80) (.split 4 (849 / 400) (.split 0 (1137 / 800) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.cycle 4 [(.pair 4 0 332), (.pair 0 1 331), (.pair 1 2 162), (.support 2 4 31 49)]) (.cycle 4 [(.pair 4 0 332), (.pair 0 1 331), (.pair 1 2 156), (.support 2 4 28 49)])) (.split 2 (1341 / 800) (.split 3 (1239 / 800) (.split 4 (1647 / 800) (.split 0 (2223 / 1600) (.inner ![372, 156, 155, 371, 373]) (.split 1 (2733 / 1600) (.inner ![374, 167, 155, 371, 342]) (.outer ![56, 27, 31, 2, 49]))) (.cycle 2 [(.support 2 4 31 52), (.support 4 1 52 28), (.pair 1 2 156)])) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 156), (.pair 2 3 161), (.support 3 4 32 49)])) (.outer ![5, 28, 28, 2, 49]))) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.split 3 (1239 / 800) (.split 4 (1647 / 800) (.inner ![321, 162, 155, 371, 333]) (.split 0 (93 / 64) (.split 1 (2631 / 1600) (.cycle 4 [(.pair 4 0 344), (.pair 0 1 375), (.pair 1 2 171), (.support 2 4 31 52)]) (.cycle 2 [(.support 2 4 31 52), (.support 4 1 52 30), (.pair 1 2 162)])) (.split 1 (2631 / 1600) (.cycle 4 [(.pair 4 0 316), (.pair 0 1 345), (.pair 1 2 171), (.support 2 4 31 52)]) (.cycle 2 [(.support 2 4 31 52), (.support 4 1 52 30), (.pair 1 2 162)])))) (.cycle 0 [(.pair 0 1 321), (.pair 1 2 162), (.pair 2 3 161), (.support 3 4 32 49), (.pair 4 0 316)])) (.split 3 (1239 / 800) (.split 4 (1647 / 800) (.cycle 4 [(.pair 4 0 333), (.pair 0 1 321), (.pair 1 2 156), (.support 2 4 28 49)]) (.cycle 2 [(.support 2 4 28 52), (.support 4 1 52 31), (.pair 1 2 156)])) (.split 4 (1647 / 800) (.cycle 4 [(.pair 4 0 333), (.pair 0 1 321), (.pair 1 2 156), (.support 2 4 28 49)]) (.cycle 2 [(.support 2 4 28 52), (.support 4 1 52 31), (.pair 1 2 156)])))) (.split 2 (1341 / 800) (.split 3 (1239 / 800) (.split 4 (1647 / 800) (.split 0 (93 / 64) (.split 1 (2733 / 1600) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 167), (.pair 2 3 155), (.pair 3 4 371)]) (.outer ![7, 27, 31, 2, 49])) (.split 1 (2733 / 1600) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 167), (.pair 2 3 155), (.pair 3 4 371)]) (.outer ![16, 27, 31, 2, 49]))) (.cycle 2 [(.support 2 4 31 52), (.support 4 1 52 28), (.pair 1 2 156)])) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 156), (.pair 2 3 161), (.support 3 4 32 49)])) (.outer ![7, 28, 28, 2, 49])))) (.split 0 (1137 / 800) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.cycle 2 [(.support 2 4 31 50), (.support 4 1 50 31), (.pair 1 2 162)]) (.outer ![5, 31, 28, 2, 50])) (.outer ![5, 28, 31, 2, 50])) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.cycle 2 [(.support 2 4 31 50), (.support 4 1 50 31), (.pair 1 2 162)]) (.outer ![7, 31, 28, 2, 50])) (.outer ![7, 28, 31, 2, 50])))) (.split 4 (849 / 400) (.split 0 (1137 / 800) (.split 1 (1341 / 800) (.cycle 0 [(.pair 0 1 331), (.pair 1 2 156), (.pair 2 3 1), (.support 3 4 31 49), (.pair 4 0 332)]) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 1), (.pair 2 3 1), (.support 3 4 31 49)])) (.split 1 (1341 / 800) (.cycle 0 [(.pair 0 1 321), (.pair 1 2 156), (.pair 2 3 1), (.support 3 4 31 49), (.pair 4 0 316)]) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 1), (.pair 2 3 1), (.support 3 4 31 49)]))) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 1), (.pair 2 3 1), (.support 3 4 31 50)]))))))))))

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk50Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk50Box k10p15chunk50Tree = true := by
  apply k10ModelCoverCheck_split_true
  · apply k10ModelCoverCheck_split_true
    · decide +kernel
    · apply k10ModelCoverCheck_split_true
      · apply k10ModelCoverCheck_split_true
        · decide +kernel
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
          · apply k10ModelCoverCheck_split_true
            · decide +kernel
            · apply k10ModelCoverCheck_split_true
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
        · apply k10ModelCoverCheck_split_true
          · decide +kernel
          · apply k10ModelCoverCheck_split_true
            · decide +kernel
            · decide +kernel
      · apply k10ModelCoverCheck_split_true
        · decide +kernel
        · apply k10ModelCoverCheck_split_true
          · apply k10ModelCoverCheck_split_true
            · decide +kernel
            · apply k10ModelCoverCheck_split_true
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
          · apply k10ModelCoverCheck_split_true
            · decide +kernel
            · apply k10ModelCoverCheck_split_true
              · decide +kernel
              · apply k10ModelCoverCheck_split_true
                · decide +kernel
                · apply k10ModelCoverCheck_split_true
                  · decide +kernel
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
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
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · decide +kernel
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · decide +kernel
                    · apply k10ModelCoverCheck_split_true
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
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · decide +kernel
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
                    · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · decide +kernel
                  · decide +kernel
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
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                      · decide +kernel
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
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
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
            · decide +kernel
            · apply k10ModelCoverCheck_split_true
              · decide +kernel
              · apply k10ModelCoverCheck_split_true
                · apply k10ModelCoverCheck_split_true
                  · decide +kernel
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
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
                · decide +kernel
                · decide +kernel
            · apply k10ModelCoverCheck_split_true
              · apply k10ModelCoverCheck_split_true
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
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
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
                        · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · apply k10ModelCoverCheck_split_true
                              · decide +kernel
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · apply k10ModelCoverCheck_split_true
                              · decide +kernel
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · apply k10ModelCoverCheck_split_true
                              · decide +kernel
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
                            · apply k10ModelCoverCheck_split_true
                              · decide +kernel
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                          · decide +kernel
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
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
              · apply k10ModelCoverCheck_split_true
                · decide +kernel
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
                      · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · decide +kernel
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
                      · decide +kernel
                      · decide +kernel
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
                  · decide +kernel
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
                  · decide +kernel
                · decide +kernel
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
                            · apply k10ModelCoverCheck_split_true
                              · decide +kernel
                              · apply k10ModelCoverCheck_split_true
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
                            · decide +kernel
                            · apply k10ModelCoverCheck_split_true
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
                              · apply k10ModelCoverCheck_split_true
                                · decide +kernel
                                · decide +kernel
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
                        · decide +kernel
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
                      · decide +kernel
                      · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · decide +kernel
                  · decide +kernel


def k10p15chunk51Box : Certificate.ClosedBox 5 := ⟨![(297 / 200), (123 / 100), (123 / 100), (123 / 100), (87 / 50)], ![(87 / 50), (297 / 200), (87 / 50), (87 / 50), (9 / 4)]⟩
def k10p15chunk51Tree : K10ModelCover := (.split 2 (297 / 200) (.split 3 (297 / 200) (.inner ![152, 303, 303, 305, 304]) (.split 4 (399 / 200) (.inner ![152, 303, 152, 311, 311]) (.split 0 (129 / 80) (.cycle 0 [(.pair 0 1 310), (.pair 1 2 303), (.pair 2 3 152), (.support 3 4 2 49), (.support 4 0 49 2)]) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 303), (.pair 2 3 152), (.support 3 4 2 49), (.support 4 0 49 31)])))) (.split 3 (297 / 200) (.split 4 (399 / 200) (.inner ![152, 152, 152, 306, 311]) (.split 0 (129 / 80) (.split 1 (543 / 400) (.inner ![313, 309, 152, 305, 312]) (.split 2 (129 / 80) (.inner ![310, 310, 310, 305, 312]) (.split 3 (543 / 400) (.split 4 (849 / 400) (.inner ![310, 152, 309, 315, 314]) (.cycle 4 [(.support 4 0 50 2), (.pair 0 1 310), (.pair 1 2 152), (.support 2 4 31 50)])) (.split 4 (849 / 400) (.inner ![310, 152, 152, 316, 314]) (.cycle 4 [(.support 4 0 50 2), (.pair 0 1 310), (.pair 1 2 152), (.support 2 4 31 50)]))))) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 152), (.pair 2 3 152), (.support 3 4 0 49), (.support 4 0 49 31)]))) (.split 4 (399 / 200) (.split 0 (129 / 80) (.split 1 (543 / 400) (.inner ![313, 309, 1, 311, 348]) (.split 2 (129 / 80) (.inner ![310, 310, 154, 311, 348]) (.split 3 (129 / 80) (.inner ![310, 152, 154, 348, 348]) (.cycle 0 [(.pair 0 1 310), (.pair 1 2 152), (.pair 2 3 1), (.support 3 4 31 54), (.pair 4 0 348)])))) (.split 1 (543 / 400) (.cycle 0 [(.pair 0 1 309), (.pair 1 2 309), (.pair 2 3 1), (.pair 3 4 311), (.support 4 0 54 31)]) (.split 2 (129 / 80) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 310), (.pair 2 3 154), (.pair 3 4 311), (.support 4 0 54 31)]) (.split 3 (129 / 80) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 152), (.pair 2 3 154), (.pair 3 4 348), (.support 4 0 54 31)]) (.split 4 (747 / 400) (.split 0 (1341 / 800) (.inner ![321, 152, 1, 134, 362]) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 152), (.pair 2 3 1), (.support 3 4 31 54), (.support 4 0 54 28)])) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 152), (.pair 2 3 1), (.support 3 4 31 53), (.support 4 0 53 31)])))))) (.split 0 (129 / 80) (.split 1 (543 / 400) (.split 2 (129 / 80) (.cycle 0 [(.pair 0 1 313), (.pair 1 2 313), (.pair 2 3 154), (.support 3 4 2 49), (.support 4 0 49 2)]) (.cycle 4 [(.support 4 0 49 2), (.pair 0 1 313), (.pair 1 2 309), (.support 2 4 31 49)])) (.split 2 (129 / 80) (.split 3 (129 / 80) (.split 4 (849 / 400) (.inner ![310, 310, 153, 314, 314]) (.cycle 0 [(.pair 0 1 310), (.pair 1 2 310), (.pair 2 3 153), (.support 3 4 2 50), (.support 4 0 50 2)])) (.cycle 0 [(.pair 0 1 310), (.pair 1 2 310), (.pair 2 3 154), (.support 3 4 31 49), (.support 4 0 49 2)])) (.split 3 (129 / 80) (.split 4 (849 / 400) (.cycle 4 [(.pair 4 0 314), (.pair 0 1 310), (.pair 1 2 152), (.support 2 4 31 49)]) (.cycle 4 [(.support 4 0 50 2), (.pair 0 1 310), (.pair 1 2 152), (.support 2 4 31 50)])) (.cycle 0 [(.pair 0 1 310), (.pair 1 2 152), (.pair 2 3 1), (.support 3 4 31 49), (.support 4 0 49 2)])))) (.split 1 (543 / 400) (.cycle 0 [(.pair 0 1 309), (.pair 1 2 309), (.pair 2 3 1), (.support 3 4 2 49), (.support 4 0 49 31)]) (.split 2 (129 / 80) (.cycle 0 [(.pair 0 1 152), (.pair 1 2 310), (.pair 2 3 154), (.support 3 4 2 49), (.support 4 0 49 31)]) (.cycle 4 [(.support 4 0 49 31), (.pair 0 1 152), (.pair 1 2 152), (.support 2 4 31 49)])))))))

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk51Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk51Box k10p15chunk51Tree = true := by
  apply k10ModelCoverCheck_split_true
  · apply k10ModelCoverCheck_split_true
    · decide +kernel
    · apply k10ModelCoverCheck_split_true
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
          · apply k10ModelCoverCheck_split_true
            · decide +kernel
            · apply k10ModelCoverCheck_split_true
              · apply k10ModelCoverCheck_split_true
                · decide +kernel
                · decide +kernel
              · apply k10ModelCoverCheck_split_true
                · decide +kernel
                · decide +kernel
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
          · decide +kernel
          · apply k10ModelCoverCheck_split_true
            · decide +kernel
            · decide +kernel


def k10p15chunk52Box : Certificate.ClosedBox 5 := ⟨![(297 / 200), (297 / 200), (123 / 100), (123 / 100), (87 / 50)], ![(87 / 50), (87 / 50), (297 / 200), (87 / 50), (9 / 4)]⟩
def k10p15chunk52Tree : K10ModelCover := (.split 3 (297 / 200) (.split 4 (399 / 200) (.inner ![1, 152, 303, 306, 311]) (.split 0 (129 / 80) (.split 1 (129 / 80) (.inner ![153, 310, 303, 305, 312]) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 152), (.pair 2 3 303), (.support 3 4 0 49)])) (.cycle 0 [(.pair 0 1 1), (.pair 1 2 152), (.pair 2 3 303), (.support 3 4 0 49), (.support 4 0 49 31)]))) (.split 4 (399 / 200) (.split 0 (129 / 80) (.split 1 (129 / 80) (.inner ![153, 310, 152, 311, 348]) (.split 2 (543 / 400) (.inner ![154, 309, 309, 311, 348]) (.split 3 (129 / 80) (.inner ![154, 152, 310, 348, 348]) (.cycle 0 [(.pair 0 1 154), (.pair 1 2 152), (.pair 2 3 152), (.support 3 4 31 54), (.pair 4 0 348)])))) (.split 1 (129 / 80) (.cycle 0 [(.pair 0 1 154), (.pair 1 2 310), (.pair 2 3 152), (.pair 3 4 311), (.support 4 0 54 31)]) (.split 2 (543 / 400) (.cycle 0 [(.pair 0 1 1), (.pair 1 2 309), (.pair 2 3 309), (.pair 3 4 311), (.support 4 0 54 31)]) (.split 3 (129 / 80) (.cycle 0 [(.pair 0 1 1), (.pair 1 2 152), (.pair 2 3 310), (.pair 3 4 348), (.support 4 0 54 31)]) (.split 4 (747 / 400) (.split 0 (1341 / 800) (.cycle 0 [(.pair 0 1 156), (.pair 1 2 152), (.pair 2 3 152), (.support 3 4 31 54), (.support 4 0 54 31)]) (.cycle 0 [(.pair 0 1 1), (.pair 1 2 152), (.pair 2 3 152), (.support 3 4 31 54), (.support 4 0 54 28)])) (.cycle 4 [(.support 4 1 53 31), (.pair 1 2 152), (.pair 2 3 152), (.support 3 4 31 53)])))))) (.split 0 (129 / 80) (.split 1 (129 / 80) (.split 2 (543 / 400) (.cycle 0 [(.pair 0 1 153), (.pair 1 2 313), (.pair 2 3 309), (.support 3 4 2 49), (.support 4 0 49 2)]) (.split 3 (129 / 80) (.split 4 (849 / 400) (.inner ![153, 310, 310, 314, 314]) (.cycle 0 [(.pair 0 1 153), (.pair 1 2 310), (.pair 2 3 310), (.support 3 4 2 50), (.support 4 0 50 2)])) (.cycle 0 [(.pair 0 1 153), (.pair 1 2 310), (.pair 2 3 152), (.support 3 4 31 49), (.support 4 0 49 2)]))) (.split 2 (543 / 400) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 309), (.pair 2 3 309), (.support 3 4 2 49)]) (.split 3 (129 / 80) (.split 4 (849 / 400) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 152), (.pair 2 3 310), (.pair 3 4 314)]) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 152), (.pair 2 3 310), (.support 3 4 2 50)])) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 152), (.pair 2 3 152), (.support 3 4 31 49)])))) (.split 1 (129 / 80) (.cycle 0 [(.pair 0 1 154), (.pair 1 2 310), (.pair 2 3 152), (.support 3 4 2 49), (.support 4 0 49 31)]) (.split 2 (543 / 400) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 309), (.pair 2 3 309), (.support 3 4 2 49)]) (.split 3 (129 / 80) (.cycle 0 [(.pair 0 1 1), (.pair 1 2 152), (.pair 2 3 310), (.support 3 4 2 49), (.support 4 0 49 31)]) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 152), (.pair 2 3 152), (.support 3 4 31 49)])))))))

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk52Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk52Box k10p15chunk52Tree = true := by
  apply k10ModelCoverCheck_split_true
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
            · apply k10ModelCoverCheck_split_true
              · apply k10ModelCoverCheck_split_true
                · decide +kernel
                · decide +kernel
              · decide +kernel
    · apply k10ModelCoverCheck_split_true
      · apply k10ModelCoverCheck_split_true
        · apply k10ModelCoverCheck_split_true
          · decide +kernel
          · apply k10ModelCoverCheck_split_true
            · apply k10ModelCoverCheck_split_true
              · decide +kernel
              · decide +kernel
            · decide +kernel
        · apply k10ModelCoverCheck_split_true
          · decide +kernel
          · apply k10ModelCoverCheck_split_true
            · apply k10ModelCoverCheck_split_true
              · decide +kernel
              · decide +kernel
            · decide +kernel
      · apply k10ModelCoverCheck_split_true
        · decide +kernel
        · apply k10ModelCoverCheck_split_true
          · decide +kernel
          · apply k10ModelCoverCheck_split_true
            · decide +kernel
            · decide +kernel


def k10p15chunk53Box : Certificate.ClosedBox 5 := ⟨![(297 / 200), (297 / 200), (297 / 200), (123 / 100), (87 / 50)], ![(87 / 50), (87 / 50), (87 / 50), (297 / 200), (9 / 4)]⟩
def k10p15chunk53Tree : K10ModelCover := (.split 4 (399 / 200) (.split 0 (129 / 80) (.split 1 (129 / 80) (.inner ![153, 154, 152, 306, 348]) (.split 2 (129 / 80) (.inner ![154, 154, 310, 306, 348]) (.split 3 (543 / 400) (.split 4 (747 / 400) (.inner ![154, 1, 309, 151, 133]) (.split 0 (1239 / 800) (.inner ![157, 1, 309, 317, 350]) (.split 1 (1341 / 800) (.inner ![161, 156, 309, 317, 348]) (.cycle 4 [(.support 4 1 53 28), (.pair 1 2 1), (.pair 2 3 309), (.pair 3 4 317)])))) (.split 4 (747 / 400) (.inner ![154, 1, 152, 318, 133]) (.split 0 (1239 / 800) (.split 1 (1341 / 800) (.inner ![155, 156, 152, 306, 350]) (.split 2 (1341 / 800) (.inner ![157, 156, 321, 306, 350]) (.split 3 (1137 / 800) (.split 4 (309 / 160) (.inner ![157, 1, 319, 353, 352]) (.cycle 4 [(.support 4 1 51 28), (.pair 1 2 1), (.pair 2 3 319), (.pair 3 4 320)])) (.split 4 (309 / 160) (.inner ![157, 1, 152, 322, 352]) (.split 0 (2427 / 1600) (.split 1 (2733 / 1600) (.split 2 (2733 / 1600) (.inner ![382, 170, 325, 306, 383]) (.outer ![2, 28, 27, 7, 51])) (.outer ![2, 27, 28, 7, 51])) (.split 1 (2733 / 1600) (.split 2 (2733 / 1600) (.inner ![159, 170, 325, 306, 350]) (.outer ![15, 28, 27, 7, 51])) (.outer ![15, 27, 28, 7, 51]))))))) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.inner ![161, 162, 321, 306, 348]) (.split 3 (1137 / 800) (.cycle 0 [(.pair 0 1 161), (.pair 1 2 156), (.pair 2 3 319), (.pair 3 4 320), (.support 4 0 53 32)]) (.split 4 (309 / 160) (.inner ![161, 156, 152, 322, 355]) (.split 0 (2529 / 1600) (.split 1 (2631 / 1600) (.inner ![384, 166, 152, 306, 385]) (.split 2 (2733 / 1600) (.inner ![163, 167, 325, 306, 385]) (.cycle 4 [(.support 4 0 51 32), (.pair 0 1 163), (.pair 1 2 156), (.support 2 4 27 51)]))) (.cycle 0 [(.pair 0 1 161), (.pair 1 2 156), (.pair 2 3 152), (.pair 3 4 306), (.support 4 0 51 29)]))))) (.split 2 (1341 / 800) (.cycle 4 [(.support 4 1 53 28), (.pair 1 2 156), (.pair 2 3 321), (.pair 3 4 306)]) (.split 3 (1137 / 800) (.split 4 (309 / 160) (.inner ![154, 1, 319, 353, 355]) (.cycle 4 [(.support 4 1 51 28), (.pair 1 2 1), (.pair 2 3 319), (.pair 3 4 320)])) (.split 4 (309 / 160) (.split 0 (2529 / 1600) (.split 1 (2733 / 1600) (.inner ![169, 160, 152, 322, 387]) (.cycle 4 [(.support 4 1 53 27), (.support 1 2 27 28), (.pair 2 3 152), (.pair 3 4 322)])) (.split 1 (2733 / 1600) (.cycle 0 [(.pair 0 1 168), (.pair 1 2 160), (.pair 2 3 152), (.pair 3 4 322), (.support 4 0 53 29)]) (.cycle 4 [(.support 4 1 53 27), (.support 1 2 27 28), (.pair 2 3 152), (.pair 3 4 322)]))) (.split 0 (2529 / 1600) (.split 1 (2733 / 1600) (.split 2 (2733 / 1600) (.cycle 4 [(.support 4 1 51 28), (.pair 1 2 170), (.pair 2 3 325), (.pair 3 4 306)]) (.outer ![32, 28, 27, 7, 51])) (.outer ![32, 27, 28, 7, 51])) (.split 1 (2733 / 1600) (.cycle 0 [(.pair 0 1 168), (.pair 1 2 160), (.pair 2 3 152), (.pair 3 4 306), (.support 4 0 51 29)]) (.outer ![29, 27, 28, 7, 51])))))))))))) (.split 1 (129 / 80) (.split 2 (129 / 80) (.inner ![154, 153, 310, 306, 311]) (.split 3 (543 / 400) (.inner ![154, 154, 309, 317, 311]) (.split 4 (747 / 400) (.inner ![154, 154, 152, 318, 134]) (.cycle 0 [(.pair 0 1 154), (.pair 1 2 154), (.pair 2 3 152), (.pair 3 4 306), (.support 4 0 53 31)])))) (.split 2 (129 / 80) (.cycle 0 [(.pair 0 1 1), (.pair 1 2 154), (.pair 2 3 310), (.pair 3 4 306), (.support 4 0 54 31)]) (.split 3 (543 / 400) (.split 4 (747 / 400) (.inner ![1, 1, 309, 151, 134]) (.cycle 0 [(.pair 0 1 1), (.pair 1 2 1), (.pair 2 3 309), (.pair 3 4 317), (.support 4 0 53 31)])) (.split 4 (747 / 400) (.split 0 (1341 / 800) (.split 1 (1341 / 800) (.inner ![162, 156, 152, 318, 362]) (.split 2 (1341 / 800) (.inner ![156, 156, 321, 318, 362]) (.split 3 (1137 / 800) (.inner ![156, 1, 319, 361, 362]) (.split 4 (1443 / 800) (.inner ![156, 1, 152, 364, 363]) (.cycle 0 [(.pair 0 1 156), (.pair 1 2 1), (.pair 2 3 152), (.pair 3 4 318), (.support 4 0 55 31)]))))) (.cycle 0 [(.pair 0 1 1), (.pair 1 2 1), (.pair 2 3 152), (.pair 3 4 318), (.support 4 0 54 28)])) (.split 0 (1341 / 800) (.split 1 (1341 / 800) (.cycle 0 [(.pair 0 1 162), (.pair 1 2 156), (.pair 2 3 152), (.pair 3 4 306), (.support 4 0 53 31)]) (.split 2 (1341 / 800) (.cycle 4 [(.support 4 1 53 28), (.pair 1 2 156), (.pair 2 3 321), (.pair 3 4 306)]) (.split 3 (1137 / 800) (.cycle 0 [(.pair 0 1 156), (.pair 1 2 1), (.pair 2 3 319), (.pair 3 4 320), (.support 4 0 53 31)]) (.split 4 (309 / 160) (.cycle 0 [(.pair 0 1 156), (.pair 1 2 1), (.pair 2 3 152), (.pair 3 4 322), (.support 4 0 53 31)]) (.cycle 0 [(.pair 0 1 156), (.pair 1 2 1), (.pair 2 3 152), (.pair 3 4 306), (.support 4 0 51 31)]))))) (.cycle 0 [(.pair 0 1 1), (.pair 1 2 1), (.pair 2 3 152), (.pair 3 4 306), (.support 4 0 53 28)]))))))) (.split 0 (129 / 80) (.split 1 (129 / 80) (.split 2 (129 / 80) (.split 3 (543 / 400) (.cycle 0 [(.pair 0 1 153), (.pair 1 2 153), (.pair 2 3 313), (.pair 3 4 308), (.support 4 0 49 2)]) (.split 4 (849 / 400) (.inner ![153, 153, 310, 316, 314]) (.cycle 0 [(.pair 0 1 153), (.pair 1 2 153), (.pair 2 3 310), (.support 3 4 5 50), (.support 4 0 50 2)]))) (.split 3 (543 / 400) (.split 4 (849 / 400) (.split 0 (1239 / 800) (.inner ![366, 154, 309, 315, 367]) (.cycle 0 [(.pair 0 1 153), (.pair 1 2 154), (.pair 2 3 309), (.pair 3 4 315), (.support 4 0 49 32)])) (.split 0 (1239 / 800) (.split 1 (1239 / 800) (.cycle 4 [(.support 4 0 50 2), (.pair 0 1 388), (.pair 1 2 157), (.support 2 4 31 50)]) (.split 2 (1341 / 800) (.cycle 0 [(.pair 0 1 366), (.pair 1 2 161), (.pair 2 3 329), (.support 3 4 0 50), (.support 4 0 50 2)]) (.outer ![2, 32, 28, 0, 50]))) (.cycle 4 [(.support 4 0 50 32), (.pair 0 1 153), (.pair 1 2 154), (.support 2 4 31 50)]))) (.split 4 (849 / 400) (.split 0 (1239 / 800) (.split 1 (1239 / 800) (.cycle 4 [(.pair 4 0 367), (.pair 0 1 388), (.pair 1 2 157), (.support 2 4 31 49)]) (.split 2 (1341 / 800) (.split 3 (1137 / 800) (.inner ![366, 161, 331, 332, 367]) (.split 4 (1647 / 800) (.inner ![366, 161, 321, 333, 371]) (.split 0 (2427 / 1600) (.inner ![389, 161, 321, 316, 390]) (.split 1 (2529 / 1600) (.inner ![391, 163, 321, 316, 367]) (.split 2 (2631 / 1600) (.inner ![366, 165, 345, 316, 367]) (.cycle 4 [(.pair 4 0 367), (.pair 0 1 366), (.pair 1 2 161), (.support 2 4 30 52)])))))) (.cycle 4 [(.pair 4 0 367), (.pair 0 1 366), (.pair 1 2 154), (.support 2 4 28 49)]))) (.cycle 4 [(.support 4 0 49 32), (.pair 0 1 153), (.pair 1 2 154), (.support 2 4 31 49)])) (.split 0 (1239 / 800) (.split 1 (1239 / 800) (.cycle 4 [(.support 4 0 50 2), (.pair 0 1 388), (.pair 1 2 157), (.support 2 4 31 50)]) (.split 2 (1341 / 800) (.cycle 4 [(.support 4 0 50 2), (.pair 0 1 366), (.pair 1 2 161), (.support 2 4 31 50)]) (.outer ![2, 32, 28, 5, 50]))) (.cycle 4 [(.support 4 0 50 32), (.pair 0 1 153), (.pair 1 2 154), (.support 2 4 31 50)]))))) (.split 2 (129 / 80) (.split 3 (543 / 400) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 154), (.pair 2 3 313), (.pair 3 4 308)]) (.split 4 (849 / 400) (.split 0 (1239 / 800) (.split 1 (1341 / 800) (.inner ![155, 161, 310, 316, 367]) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 154), (.pair 2 3 310), (.pair 3 4 316)])) (.cycle 0 [(.pair 0 1 154), (.pair 1 2 154), (.pair 2 3 310), (.pair 3 4 316), (.support 4 0 49 32)])) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 154), (.pair 2 3 310), (.support 3 4 5 50)]))) (.split 3 (543 / 400) (.split 4 (849 / 400) (.split 0 (1239 / 800) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.inner ![155, 162, 329, 315, 367]) (.split 3 (207 / 160) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 156), (.pair 2 3 327), (.pair 3 4 330)]) (.split 4 (1647 / 800) (.inner ![155, 156, 309, 334, 371]) (.cycle 2 [(.support 2 4 28 52), (.support 4 1 52 31), (.pair 1 2 156)])))) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 1), (.pair 2 3 309), (.pair 3 4 315)])) (.split 1 (1341 / 800) (.cycle 0 [(.pair 0 1 161), (.pair 1 2 156), (.pair 2 3 309), (.pair 3 4 315), (.support 4 0 49 32)]) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 1), (.pair 2 3 309), (.pair 3 4 315)]))) (.split 0 (1239 / 800) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.cycle 4 [(.support 4 1 50 31), (.pair 1 2 162), (.pair 2 3 329), (.support 3 4 0 50)]) (.outer ![2, 31, 28, 0, 50])) (.outer ![2, 28, 31, 0, 50])) (.split 1 (1341 / 800) (.cycle 4 [(.support 4 0 50 32), (.pair 0 1 161), (.pair 1 2 156), (.support 2 4 31 50)]) (.outer ![32, 28, 31, 0, 50])))) (.split 4 (849 / 400) (.split 0 (1239 / 800) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.split 3 (1137 / 800) (.cycle 4 [(.support 4 1 49 31), (.pair 1 2 162), (.pair 2 3 331), (.pair 3 4 332)]) (.split 4 (1647 / 800) (.inner ![155, 162, 321, 333, 371]) (.split 0 (2427 / 1600) (.split 1 (2631 / 1600) (.split 2 (2631 / 1600) (.inner ![393, 178, 345, 316, 390]) (.cycle 2 [(.support 2 4 30 52), (.support 4 1 52 31), (.pair 1 2 171)])) (.cycle 4 [(.support 4 1 52 30), (.pair 1 2 162), (.pair 2 3 321), (.pair 3 4 316)])) (.split 1 (2631 / 1600) (.split 2 (2631 / 1600) (.inner ![376, 178, 345, 316, 367]) (.cycle 2 [(.support 2 4 30 52), (.support 4 1 52 31), (.pair 1 2 171)])) (.cycle 4 [(.support 4 1 52 30), (.pair 1 2 162), (.pair 2 3 321), (.pair 3 4 316)]))))) (.split 3 (1137 / 800) (.split 4 (1647 / 800) (.split 0 (2427 / 1600) (.inner ![394, 156, 319, 342, 396]) (.split 1 (2631 / 1600) (.inner ![376, 166, 319, 342, 371]) (.cycle 2 [(.support 2 4 28 49), (.support 4 1 49 30), (.pair 1 2 156)]))) (.cycle 2 [(.support 2 4 28 52), (.support 4 1 52 31), (.pair 1 2 156)])) (.split 4 (1647 / 800) (.split 0 (2427 / 1600) (.cycle 4 [(.pair 4 0 396), (.pair 0 1 394), (.pair 1 2 156), (.support 2 4 28 49)]) (.split 1 (2631 / 1600) (.cycle 4 [(.pair 4 0 371), (.pair 0 1 376), (.pair 1 2 166), (.support 2 4 28 49)]) (.cycle 2 [(.support 2 4 28 49), (.support 4 1 49 30), (.pair 1 2 156)]))) (.cycle 2 [(.support 2 4 28 52), (.support 4 1 52 31), (.pair 1 2 156)])))) (.split 2 (1341 / 800) (.split 3 (1137 / 800) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 156), (.pair 2 3 331), (.pair 3 4 332)]) (.split 4 (1647 / 800) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 156), (.pair 2 3 321), (.pair 3 4 333)]) (.cycle 4 [(.support 4 1 52 28), (.pair 1 2 156), (.pair 2 3 321), (.pair 3 4 316)]))) (.outer ![2, 28, 28, 5, 49]))) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.cycle 0 [(.pair 0 1 161), (.pair 1 2 162), (.pair 2 3 321), (.pair 3 4 316), (.support 4 0 49 32)]) (.cycle 4 [(.support 4 0 49 32), (.pair 0 1 161), (.pair 1 2 156), (.support 2 4 28 49)])) (.split 2 (1341 / 800) (.split 3 (1137 / 800) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 156), (.pair 2 3 331), (.pair 3 4 332)]) (.split 4 (1647 / 800) (.cycle 4 [(.support 4 1 49 28), (.pair 1 2 156), (.pair 2 3 321), (.pair 3 4 333)]) (.cycle 4 [(.support 4 1 52 28), (.pair 1 2 156), (.pair 2 3 321), (.pair 3 4 316)]))) (.outer ![32, 28, 28, 5, 49])))) (.split 0 (1239 / 800) (.split 1 (1341 / 800) (.split 2 (1341 / 800) (.cycle 2 [(.support 2 4 31 50), (.support 4 1 50 31), (.pair 1 2 162)]) (.outer ![2, 31, 28, 5, 50])) (.outer ![2, 28, 31, 5, 50])) (.split 1 (1341 / 800) (.cycle 4 [(.support 4 0 50 32), (.pair 0 1 161), (.pair 1 2 156), (.support 2 4 31 50)]) (.outer ![32, 28, 31, 5, 50]))))))) (.split 1 (129 / 80) (.split 2 (129 / 80) (.cycle 0 [(.pair 0 1 154), (.pair 1 2 153), (.pair 2 3 310), (.support 3 4 0 49), (.support 4 0 49 31)]) (.cycle 4 [(.support 4 0 49 31), (.pair 0 1 154), (.pair 1 2 154), (.support 2 4 31 49)])) (.split 2 (129 / 80) (.cycle 0 [(.pair 0 1 1), (.pair 1 2 154), (.pair 2 3 310), (.support 3 4 0 49), (.support 4 0 49 31)]) (.split 3 (543 / 400) (.split 4 (849 / 400) (.cycle 0 [(.pair 0 1 1), (.pair 1 2 1), (.pair 2 3 309), (.pair 3 4 315), (.support 4 0 49 31)]) (.cycle 4 [(.support 4 0 50 31), (.pair 0 1 1), (.pair 1 2 1), (.support 2 4 31 50)])) (.split 4 (849 / 400) (.split 0 (1341 / 800) (.split 1 (1341 / 800) (.cycle 4 [(.support 4 0 49 31), (.pair 0 1 162), (.pair 1 2 156), (.support 2 4 31 49)]) (.split 2 (1341 / 800) (.cycle 0 [(.pair 0 1 156), (.pair 1 2 156), (.pair 2 3 321), (.pair 3 4 316), (.support 4 0 49 31)]) (.outer ![31, 28, 28, 5, 49]))) (.cycle 4 [(.support 4 0 49 28), (.pair 0 1 1), (.pair 1 2 1), (.support 2 4 31 49)])) (.cycle 4 [(.support 4 0 50 31), (.pair 0 1 1), (.pair 1 2 1), (.support 2 4 31 50)])))))))

/-- Exact leaf arithmetic and exhaustive closed splitting, replayed by the kernel. -/
theorem k10p15chunk53Checked :
    k10ModelCoverCheck (k10EmptyPattern 15) 57588 628319
      k10p15chunk53Box k10p15chunk53Tree = true := by
  apply k10ModelCoverCheck_split_true
  · apply k10ModelCoverCheck_split_true
    · apply k10ModelCoverCheck_split_true
      · decide +kernel
      · apply k10ModelCoverCheck_split_true
        · decide +kernel
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
                  · decide +kernel
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                        · decide +kernel
                · apply k10ModelCoverCheck_split_true
                  · decide +kernel
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
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
                            · decide +kernel
                          · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · decide +kernel
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
          · apply k10ModelCoverCheck_split_true
            · decide +kernel
            · decide +kernel
          · apply k10ModelCoverCheck_split_true
            · apply k10ModelCoverCheck_split_true
              · apply k10ModelCoverCheck_split_true
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
                  · decide +kernel
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · decide +kernel
              · decide +kernel
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
            · apply k10ModelCoverCheck_split_true
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
              · apply k10ModelCoverCheck_split_true
                · decide +kernel
                · apply k10ModelCoverCheck_split_true
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · apply k10ModelCoverCheck_split_true
                        · decide +kernel
                        · apply k10ModelCoverCheck_split_true
                          · decide +kernel
                          · apply k10ModelCoverCheck_split_true
                            · decide +kernel
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
                  · apply k10ModelCoverCheck_split_true
                    · decide +kernel
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · decide +kernel
                · decide +kernel
              · apply k10ModelCoverCheck_split_true
                · decide +kernel
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
                        · decide +kernel
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
                    · apply k10ModelCoverCheck_split_true
                      · decide +kernel
                      · decide +kernel
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
    · apply k10ModelCoverCheck_split_true
      · apply k10ModelCoverCheck_split_true
        · decide +kernel
        · decide +kernel
      · apply k10ModelCoverCheck_split_true
        · decide +kernel
        · apply k10ModelCoverCheck_split_true
          · apply k10ModelCoverCheck_split_true
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


end CP15
