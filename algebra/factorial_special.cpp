#include <stdio.h>

#include "modint.h"

constexpr int FACTORIAL_STEP = 1'000'000;

constexpr ModInt<998244353> FACTORIAL[] = {1,373341033,45596018,834980587,623627864,428937595,442819817,499710224,833655840,83857087,295201906,788488293,671639287,849315549,597398273,813259672,732727656,244038325,122642896,310517972,160030060,483239722,683879839,712910418,384710263,433880730,844360005,513089677,101492974,959253371,957629942,678615452,34035221,56734233,524027922,31729117,102311167,330331487,8332991,832392662,545208507,594075875,318497156,859275605,300738984,767818091,864118508,878131539,316588744,812496962,213689172,584871249,980836133,54096741,417876813,363266670,335481797,730839588,393495668,435793297,760025067,811438469,720976283,650770098,586537547,117371703,566486504,749562308,708205284,932912293,939830261,983699513,206579820,301188781,593164676,770845925,247687458,41047791,266419267,937835947,506268060,6177705,936268003,166873118,443834893,328979964,470135404,954410105,117565665,832761782,39806322,478922755,394880724,821825588,468705875,512554988,232240472,876497899,356048018,895187265,808258749,575505950,68190615,939065335,552199946,694814243,385460530,529769387,640377761,916128300,440133909,362216114,826373774,502324157,457648395,385510728,904737188,78988746,454565719,623828097,686156489,713476044,63602402,570334625,681055904,222059821,477211096,343363294,833792655,461853093,741797144,74731896,930484262,268372735,941222802,677432735,474842829,700451655,400176109,697644778,390377694,790010794,360642718,505712943,946647976,339045014,715797300,251680896,70091750,40517433,12629586,850635539,110877109,571935891,695965747,634938288,69072133,155093216,749696762,963086402,544711799,724471925,334646013,574791029,722417626,377929821,743946412,988034679,405207112,18063742,104121967,638607426,607304611,751377777,35834555,313632531,18058363,656121134,40763559,562910912,495867250,48767038,210864657,659137294,715390025,865854329,324322857,388911184,286059202,636456178,421290700,832276048,726437551,526417714,252522639,386147469,674313019,274769381,226519400,272047186,117153405,712896591,486826649,119444874,338909703,18536028,41814114,245606459,140617938,250512392,57084755,157807456,261113192,40258068,194807105,325341339,884328111,896332013,880836012,737358206,202713771,785454372,399586250,485457499,640827004,546969497,749602473,159788463,159111724,218592929,675932866,314795475,811539323,246883213,696818315,759880589,4302336,353070689,477909706,559289160,79781699,878094972,840903973,367416824,973366814,848259019,462421750,667227759,897917455,81800722,956276337,942686845,420541799,417005912,272641764,941778993,217214373,192220616,267901132,50530621,652678397,354880856,164289049,781023184,105376215,315094878,607856504,733905911,457743498,992735713,35212756,231822660,276036750,734558079,424180850,433186147,308380947,18333316,12935086,351491725,655645460,535812389,521902115,67016984,48682076,64748124,489360447,361275315,786336279,805161272,468129309,645091350,887284732,913004502,358814684,281295633,328970139,395955130,164840186,820902807,761699708,246274415,592331769,913846362,866682684,600130702,903837674,529462989,90612675,526540127,533047427,110008879,674279751,801920753,645226926,676886948,752481486,474034007,457790341,166813684,287671032,188118664,244731384,404032157,269766986,423996017,182948540,356801634,737863144,652014069,206068022,504569410,919894484,593398649,963768176,882517476,702523597,949028249,128957299,171997372,50865043,20937461,690959202,581356488,369182214,993580422,193500140,540665426,365786018,743731625,144980423,979536721,773259009,617053935,247670131,843705280,30419459,985463402,261585206,237885042,111276893,488166208,137660292,720784236,244467770,26368504,792857103,666885724,670313309,905683034,259415897,512017253,826265493,111960112,633652060,918048438,516432938,386972415,996212724,610073831,444094191,72480267,665038087,11584804,301029012,723617861,113763819,778259899,937766095,535448641,593907889,783573565,673298635,599533244,655712590,173350007,868198597,169013813,585161712,697502214,573994984,285943986,675831407,3134056,965907646,401920943,665949756,236277883,612745912,813282113,892454686,901222267,624900982,927122298,686321335,84924870,927606072,506664166,353631992,165913238,566073550,816674343,864877926,171259407,908752311,874007723,803597299,613676466,880336545,282280109,128761001,58852065,474075900,434816091,364856903,149123648,388854780,314693916,423183826,419733481,888483202,238933227,336564048,757103493,100189123,855479832,51370348,403061033,496971759,831753030,251718753,272779384,683379259,488844621,881783783,659478190,445719559,740782647,546525906,985524427,548033568,333772553,331916427,752533273,730387628,93829695,655989476,930661318,334885743,466041862,428105027,888238707,232218076,769865249,730641039,616996159,231721356,326973501,426068899,722403656,742756734,663270261,364187931,350431704,671823672,633125919,226166717,386814657,237594135,451479365,546182474,119366536,465211069,605313606,728508871,249619035,663053607,900453742,48293872,229958401,62402409,69570431,71921532,960467929,537087913,514588945,513856225,415497414,286592050,645469437,102052166,163298189,873938719,617583886,986843080,962390239,580971332,665147020,88900164,89866970,826426395,616059995,443012312,659160562,229855967,687413213,59809521,398599610,325666688,154765991,159186619,210830877,386454418,84493735,974220646,820097297,2191828,481459931,729073424,551556379,926316039,151357011,808637654,218058015,786112034,850407126,84202800,94214098,30019651,121701603,176055335,865461951,553631971,286620803,984061713,888573766,302767023,977070668,110954576,83922475,51568171,60949367,19533020,510592752,615419476,341370469,912573425,286207526,206707897,384156962,414163604,193301813,749570167,366933789,11470970,600191572,391667731,328736286,30645366,215162519,604947226,236199953,718439098,411423177,803407599,632441623,766760224,263006576,757681534,61082578,681666415,947466395,12206799,659767098,933746852,978860867,59215985,161179205,439197472,259779111,511621808,145770512,882749888,943124465,872053396,631078482,166861622,743415395,772287179,602427948,924112080,385643091,794973480,883782693,869723371,805963889,313106351,262132854,400034567,488248149,265769800,791715397,408753255,468381897,415812467,172922144,64404368,281500398,512318142,288791777,955559118,242484726,536413695,205340854,707803527,576699812,218525078,875554190,46283078,833841915,763148293,807722138,788080170,556901372,150896699,253151120,97856807,918256774,771557187,582547026,472709375,911615063,743371401,641382840,446540967,184639537,157247760,775930891,939702814,499082462,19536133,548753627,593243221,563850263,185475971,687419227,396799323,657976136,864535682,433009242,860830935,33107339,517661450,467651311,812398757,202133852,431839017,709549400,99643620,773282878,290471030,61134552,129206504,929147251,837008968,422332597,353775281,469563025,62265336,835064501,851685235,21197005,264793769,326416680,118842991,84257200,763248924,687559609,150907932,401832452,242726978,766752066,959173604,390269102,992293822,744816299,476631694,177284763,702429415,374065901,169855231,629007616,719169602,564737074,475119050,714502830,40993711,820235888,749063595,239329111,612759169,18591377,419142436,442202439,941600951,158013406,637073231,471564060,447222237,701248503,599797734,577221870,69656699,51052704,6544303,10958310,554955500,943192237,192526269,897983911,961628039,240232720,627280533,710239542,70255649,261743865,228474833,776408079,304180483,63607040,953297493,758058902,395529997,156010331,825833840,539880795,234683685,52626619,751843490,116909119,62806842,574857555,353417551,40061330,822203768,681051568,490913702,9322961,766631257,124794668,37844313,163524507,729108319,490867505,47035168,682765157,53842115,817965276,757179922,339238384,909741023,150530547,158444563,140949492,993302799,551621442,137578883,475122706,443869843,605400098,689361523,769596520,801661499,474900284,586624857,349960501,134084537,650564083,877097974,379857427,887890124,159436401,133274277,986182139,729720334,568925901,459461496,499309445,493171177,460958750,380694152,168836226,840160881,141116880,225064950,109618190,842341383,85305729,759273275,97369807,669317759,766247510,829017039,550323884,261274540,918239352,29606025,870793828,293683814,378510746,367270918,481292028,813097823,798448487,230791733,899305835,504040630,162510533,479367951,275282274,806951470,462774647,56473153,184659008,905122161,664034750,109726629,59372704,325795100,486860143,843736533,924723613,880348000,801252478,616515290,776142608,284803450,583439582,274826676,6018349,377403437,244041569,527081707,544763288,708818585,354033051,904309832,589922898,673933870,682858433,945260111,899893421,515264973,911685911,9527148,239480646,524126897,48259065,578214879,118677219,786127243,869205770,923276513,937928886,802186160,12198440,638784295,34200904,758925811,185027790,80918046,120604699,610456697,573601211,208296321,49743354,653691911,490750754,674335312,887877110,875880304,308360096,414636410,886100267,8525751,636257427,558338775,500159951,696213291,97268896,364983542,937928436,641582714,586211304,345265657,994704486,443549763,207259440,302122082,166055224,623250998,239642551,476337075,283167364,211328914,68064804,950202136,187552679,18938709,646784245,598764068,538505481,610424991,864445053,390248689,278395191,686098470,935957187,868529577,329970687,804930040,84992079,474569269,810762228,573258936,756464212,155080225,286966169,283614605,19283401,24257676,871831819,612689791,846988741,617120754,971716517,979541482,297910784,991087897,783825907,214821357,689498189,405026419,946731704,609346370,707669156,457703127,957341187,980735523,649367684,791011898,82098966,234729712,105002711,130614285,291032164,193188049,363211260,58108651,100756444,954947696,346032213,863300806,36876722,622610957,289232396,667938985,734886266,395881057,417188702,183092975,887586469,83334648,797819763,100176902,781587414,841864935,371674670,18247584,};
// constexpr ModInt<1000000007> FACTORIAL[] = {1,641102369,578095319,5832229,259081142,974067448,316220877,690120224,251368199,980250487,682498929,134623568,95936601,933097914,167332441,598816162,336060741,248744620,626497524,288843364,491101308,245341950,565768255,246899319,968999,586350670,638587686,881746146,19426633,850500036,76479948,268124147,842267748,886294336,485348706,463847391,544075857,898187927,798967520,82926604,723816384,156530778,721996174,299085602,323604647,172827403,398699886,530389102,294587621,813805606,67347853,497478507,196447201,722054885,228338256,407719831,762479457,746536789,811667359,778773518,27368307,438371670,59469516,5974669,766196482,606322308,86609485,889750731,340941507,371263376,625544428,788878910,808412394,996952918,585237443,1669644,361786913,480748381,595143852,837229828,199888908,526807168,579691190,145404005,459188207,534491822,439729802,840398449,899297830,235861787,888050723,656116726,736550105,440902696,85990869,884343068,56305184,973478770,168891766,804805577,927880474,876297919,934814019,676405347,567277637,112249297,44930135,39417871,47401357,108819476,281863274,60168088,692636218,432775082,14235602,770511792,400295761,697066277,421835306,220108638,661224977,261799937,168203998,802214249,544064410,935080803,583967898,211768084,751231582,972424306,623534362,335160196,243276029,554749550,60050552,797848181,395891998,172428290,159554990,887420150,970055531,250388809,487998999,856259313,82104855,232253360,513365505,244109365,1559745,695345956,261384175,849009131,323214113,747664143,444090941,659224434,80729842,570033864,664989237,827348878,195888993,576798521,457882808,731551699,212938473,509096183,827544702,678320208,677711203,289752035,66404266,555972231,195290384,97136305,349551356,785113347,83489485,66247239,52167191,307390891,547665832,143066173,350016754,917404120,296269301,996122673,23015220,602139210,748566338,187348575,109838563,574053420,105574531,304173654,542432219,34538816,325636655,437843114,630621321,26853683,933245637,616368450,238971581,511371690,557301633,911398531,848952161,958992544,925152039,914456118,724691727,636817583,238087006,946237212,910291942,114985663,492237273,450387329,834860913,763017204,368925948,475812562,740594930,45060610,806047532,464456846,172115341,75307702,116261993,562519302,268838846,173784895,243624360,61570384,481661251,938269070,95182730,91068149,115435332,495022305,136026497,506496856,710729672,113570024,366384665,564758715,270239666,277118392,79874094,702807165,112390913,730341625,103056890,677948390,339464594,167240465,108312174,839079953,479334442,271788964,135498044,277717575,591048681,811637561,353339603,889410460,839849206,192345193,736265527,316439118,217544623,788132977,618898635,183011467,380858207,996097969,898554793,335353644,54062950,611251733,419363534,965429853,160398980,151319402,990918946,607730875,450718279,173539388,648991369,970937898,500780548,780122909,39052406,276894233,460373282,651081062,461415770,358700839,643638805,560006119,668123525,686692315,673464765,957633609,199866123,563432246,841799766,385330357,504962686,954061253,128487469,685707545,299172297,717975101,577786541,318951960,773206631,306832604,204355779,573592106,30977140,450398100,363172638,258379324,472935553,93940075,587220627,776264326,793270300,291733496,522049725,579995261,335416359,142946099,472012302,559947225,332139472,499377092,464599136,164752359,309058615,86117128,580204973,563781682,954840109,624577416,895609896,888287558,836813268,926036911,386027524,184419613,724205533,403351886,715247054,716986954,830567832,383388563,68409439,6734065,189239124,68322490,943653305,405755338,811056092,179518046,825132993,343807435,985084650,868553027,148528617,160684257,882148737,591915968,701445829,529726489,302177126,974886682,241107368,798830099,940567523,11633075,325334066,346091869,115312728,473718967,218129285,878471898,180002392,699739374,917084264,856859395,435327356,808651347,421623838,105419548,59883031,322487421,79716267,715317963,429277690,398078032,316486674,384843585,940338439,937409008,940524812,947549662,833550543,593524514,996164327,987314628,697611981,636177449,274192146,418537348,925347821,952831975,893732627,1277567,358655417,141866945,581830879,987597705,347046911,775305697,125354499,951540811,247662371,343043237,568392357,997474832,209244402,380480118,149586983,392838702,309134554,990779998,263053337,325362513,780072518,551028176,990826116,989944961,155569943,596737944,711553356,268844715,451373308,379404150,462639908,961812918,654611901,382776490,41815820,843321396,675258797,845583555,934281721,741114145,275105629,666247477,325912072,526131620,252551589,432030917,554917439,818036959,754363835,795190182,909210595,278704903,719566487,628514947,424989675,321685608,50590510,832069712,198768464,702004730,99199382,707469729,747407118,302020341,497196934,5003231,726997875,382617671,296229203,183888367,703397904,552133875,732868367,350095207,26031303,863250534,216665960,561745549,352946234,784139777,733333339,503105966,459878625,803187381,16634739,180898306,68718097,985594252,404206040,749724532,97830135,611751357,31131935,662741752,864326453,864869025,167831173,559214642,718498895,91352335,608823837,473379392,385388084,152267158,681756977,46819124,313132653,56547945,442795120,796616594,256141983,152028387,636578562,385377759,553033642,491415383,919273670,996049638,326686486,160150665,141827977,540818053,693305776,593938674,186576440,688809790,565456578,749296077,519397500,551096742,696628828,775025061,370732451,164246193,915265013,457469634,923043932,912368644,777901604,464118005,637939935,956856710,490676632,453019482,462528877,502297454,798895521,100498586,699767918,849974789,811575797,438952959,606870929,907720182,179111720,48053248,508038818,811944661,752550134,401382061,848924691,764368449,34629406,529840945,435904287,26011548,208184231,446477394,206330671,366033520,131772368,185646898,648711554,472759660,523696723,271198437,25058942,859369491,817928963,330711333,724464507,437605233,701453022,626663115,281230685,510650790,596949867,295726547,303076380,465070856,272814771,538771609,48824684,951279549,939889684,564188856,48527183,201307702,484458461,861754542,326159309,181594759,668422905,286273596,965656187,44135644,359960756,936229527,407934361,267193060,456152084,459116722,124804049,262322489,920251227,816929577,483924582,151834896,167087470,490222511,903466878,361583925,368114731,339383292,388728584,218107212,249153339,909458706,322908524,202649964,92255682,573074791,15570863,94331513,744158074,196345098,334326205,9416035,98349682,882121662,769795511,231988936,888146074,137603545,582627184,407518072,919419361,909433461,986708498,310317874,373745190,263645931,256853930,876379959,702823274,147050765,308186532,175504139,180350107,797736554,606241871,384547635,273712630,586444655,682189174,666493603,946867127,819114541,502371023,261970285,825871994,126925175,701506133,314738056,341779962,561011609,815463367,46765164,49187570,188054995,957939114,64814326,933376898,329837066,338121343,765215899,869630152,978119194,632627667,975266085,435887178,282092463,129621197,758245605,827722926,201339230,918513230,322096036,547838438,985546115,852304035,593090119,689189630,555842733,567033437,469928208,212842957,117842065,404149413,155133422,663307737,208761293,206282795,717946122,488906585,414236650,280700600,962670136,534279149,214569244,375297772,811053196,922377372,289594327,219932130,211487466,701050258,398782410,863002719,27236531,217598709,375472836,810551911,178598958,247844667,676526196,812283640,863066876,857241854,113917835,624148346,726089763,564827277,826300950,478982047,439411911,454039189,633292726,48562889,802100365,671734977,945204804,508831870,398781902,897162044,644050694,892168027,828883117,277714559,713448377,624500515,590098114,808691930,514359662,895205045,715264908,628829100,484492064,919717789,513196123,748510389,403652653,574455974,77123823,172096141,819801784,581418893,15655126,15391652,875641535,203191898,264582598,880691101,907800444,986598821,340030191,264688936,369832433,785804644,842065079,423951674,663560047,696623384,496709826,161960209,331910086,541120825,951524114,841656666,162683802,629786193,190395535,269571439,832671304,76770272,341080135,421943723,494210290,751040886,317076664,672850561,72482816,493689107,135625240,100228913,684748812,639655136,906233141,929893103,277813439,814362881,562608724,406024012,885537778,10065330,60625018,983737173,60517502,551060742,804930491,823845496,727416538,946421040,678171399,842203531,175638827,894247956,538609927,885362182,946464959,116667533,749816133,241427979,871117927,281804989,163928347,563796647,640266394,774625892,59342705,256473217,674115061,918860977,322633051,753513874,393556719,304644842,767372800,161362528,754787150,627655552,677395736,799289297,846650652,816701166,687265514,787113234,358757251,701220427,607715125,245795606,600624983,10475577,728620948,759404319,36292292,491466901,22556579,114495791,647630109,586445753,482254337,718623833,763514207,66547751,953634340,351472920,308474522,494166907,634359666,172114298,865440961,364380585,921648059,965683742,260466949,117483873,962540888,237120480,620531822,193781724,213092254,107141741,602742426,793307102,756154604,236455213,362928234,14162538,753042874,778983779,25977209,49389215,698308420,859637374,49031023,713258160,737331920,923333660,804861409,83868974,682873215,217298111,883278906,176966527,954913,105359006,390019735,10430738,706334445,315103615,567473423,708233401,48160594,946149627,346966053,281329488,462880311,31503476,185438078,965785236,992656683,916291845,881482632,899946391,321900901,512634493,303338827,121000338,967284733,492741665,152233223,165393390,680128316,917041303,532702135,741626808,496442755,536841269,131384366,377329025,301196854,859917803,676511002,373451745,847645126,823495900,576368335,73146164,954958912,847549272,241289571,646654592,216046746,205951465,3258987,780882948,822439091,598245292,869544707,698611116,};
// constexpr ModInt<1000000009> FACTORIAL[] = {1,22525129,678785054,829908825,700200833,813072024,472347344,412283487,333209387,327426984,220747438,534587905,452427869,621717439,614595800,941953454,930346515,405287699,787147627,306233418,13387514,648092371,148800528,983396557,262157038,55188328,474016079,728211065,355659639,122023833,587523700,536035789,458375857,637088927,838839412,66692878,482256340,253496280,723180240,563248211,705806641,441003259,753217810,701138212,309261951,44447730,735670669,880050291,809722347,33024553,975772137,556129676,639964497,92281133,272197877,373832935,961868764,334715630,254310803,747673331,547521639,945685573,116625453,452900637,979103046,20371947,62761976,612744181,168573906,248509462,123450291,693365908,462788082,609575552,123507657,560116236,368046826,723780419,826642909,84036051,615462151,657089216,547704614,739078586,617034925,350256714,455545816,859904282,414322256,786005699,132683924,501132470,976678556,999462986,432831476,843337530,147490927,164758970,219057611,668282305,145383407,255439711,136010517,157618750,910729174,922070514,498001402,278970846,330974383,322677218,996372752,269993821,322831045,602964614,313289432,856701527,716851044,221145862,985160535,91372382,953919163,233249400,344335444,117970417,368724557,715411082,778487345,148412800,62256905,588930028,271957352,596455472,317096615,670918482,406298031,100109960,466921159,232684521,716407705,396397853,212611745,392419615,924708046,62689778,111335283,166179733,33797403,428852874,177894915,336283592,934753973,99738060,276701708,823239208,104924784,336584398,109079574,826442828,213209139,470208627,379691161,175171625,572089642,18393015,791694095,373422760,455665006,521416944,533603163,174682348,425251567,682550036,19071162,932775958,322855183,384788952,517343125,602737093,65248355,714921014,718966394,169391750,715667784,816879202,272763287,629863519,169994082,104736191,965614917,533684606,325966971,272728327,165740666,982609189,312672800,821326694,11713077,451666228,20167232,678897556,295498983,333515180,209119486,106167825,246651392,158905203,119193090,335033260,112069712,412078088,847050754,250655767,327103973,388197652,872417738,309818277,508647585,541825148,182439839,302152447,790462395,346787342,70514714,212865006,490085756,490744599,785799039,843539545,840973656,32173344,95414895,871740768,288748185,892900525,604789476,146732028,560177994,352729226,686690586,584814998,123349002,728500203,991327041,149305054,212972920,166947556,136728354,536768720,960689943,326051510,763017660,330866933,94976139,521963894,417327356,260459206,124034983,525979183,580702058,303518436,989272159,357326482,218824495,561527432,440672655,717745600,972786205,63837770,19768222,556855885,491446877,853604083,122461351,934690068,233265108,499233684,161928730,248168977,370757035,290061419,224762564,239340713,1728261,709901461,603153413,840298186,136613026,326293020,595115975,887093668,372663754,233267500,765204247,534879747,741346335,232546013,801300441,462102245,724468385,837838746,612654084,138322415,722196139,426128942,772310190,672997010,142870549,714382819,757144071,33367586,277863305,496060040,534752029,159519911,336283581,894987518,827260577,190794016,19494047,973667364,623256211,905272395,243529007,188174957,856793859,107613046,220240648,165740235,333878571,73277876,680169909,696129273,505535864,204018949,368203446,977954144,827516100,349122194,754284453,234235468,215942355,421485859,381600491,744726640,907762837,830517158,213971989,916838355,752149615,432044515,231607220,840036790,299372160,406961704,824839098,857743295,955042387,67131286,312804683,122280541,828043697,595735397,183963973,901718500,876025818,943585557,389203615,406193436,275009954,892955356,422877898,771828335,17562111,909243361,219359026,893842936,977285031,420624313,860943640,22909616,590856298,413617587,134471436,728872126,631064160,516137331,789191254,82246922,899822662,941130695,186393835,53578192,717069546,281951729,981780273,35531117,698917617,956700342,691730117,368513025,183691628,205933398,923914174,494672703,5505440,634857765,494278726,415316854,218187219,265150593,741971064,961998659,350939495,558858694,417114803,896719218,58561688,821221519,369144971,868415894,698904592,690208644,546984177,961378423,878480719,946275399,80833219,162903938,91175258,65641496,350756030,137460346,679637223,51946726,919640173,916798219,257992457,475193562,649839352,198766665,236803450,826167780,337482242,529212931,87759108,59648344,969612429,659067932,165961542,835649587,187416035,110691134,89741269,840275440,548932298,770398174,273827699,221138593,699322033,120889871,116540604,229810609,103859422,163555247,244031942,851762867,37659871,724216707,764124756,768988290,253857263,530957300,387426230,490816138,572120396,466430286,520380378,126007979,962393238,812925322,17753364,428939727,157229613,733836959,520031954,879926478,589650168,834018605,711918618,483630039,3079544,446201703,547431089,78442894,220647510,740401275,764720057,355267017,443189713,866343003,115355779,297436279,93164201,808069521,458245581,71670024,480874858,592405608,449958785,323321795,975941920,342056182,257336542,48191468,467129717,424794421,695859582,754036403,718464778,275413181,184449544,639779255,691189327,544264765,92092999,904381465,998821728,745808334,414750349,277620492,7585528,846304180,843955233,355647898,609721049,617312586,512515129,989122442,349576252,78289392,322369961,342250009,31311262,113396989,540764230,371990702,139597278,429832047,962479609,772069164,890197982,770892459,13996613,732588562,528211850,650696862,947199417,875517747,923592684,683541131,845666129,350569266,150209477,349496514,418380523,390287077,787798646,129655256,536382873,502351675,903193206,143193281,561287023,19224021,723412512,61036807,671982005,520712112,97264575,86795295,600233786,567844553,792855383,182319804,669441785,903616246,166902048,881801876,194045714,774833202,108414639,583078287,219039157,195441792,260095963,500380341,521107915,358677894,665894562,795788764,76695227,633434296,446352141,460045616,154011287,33838089,638210873,878127808,17819338,940287176,10498072,225795516,67212319,641817267,377967209,364420582,627126171,274228756,283341937,499562939,435268292,38412785,953509216,111961598,597797290,632573336,931433616,797255842,30434078,881381061,472609118,629729798,277558026,904440738,521613453,90832979,4950108,518138915,762896824,45630308,359558818,867969761,505831216,46496046,582698742,843103163,313707223,34010089,497929578,576873321,391162040,801197154,905213741,161467329,815731456,854382086,58320224,711310564,83684589,932615609,772460756,364840176,505294133,809124509,398431578,413450400,422245456,952040149,393759353,514374020,769199748,795906988,710916435,865298095,4037219,95517052,433292166,817632277,825563152,522489944,997987438,245946015,906727924,320797490,245696143,379446169,662093325,917151591,560052846,960849816,543047223,180069858,903414518,296863576,969774214,712679710,927439502,846298119,706300148,562737172,715745761,162909198,308759524,424142769,809100910,165306517,102288102,906306504,154635423,117604720,959330894,574756887,703257223,618333243,346379366,39928756,222900813,293480043,271562783,736443487,879669636,555720296,308597321,479797333,464560006,335102985,971133954,548181809,832294302,209887176,500982316,301262344,188270638,920279962,203302568,112972872,996203120,857403920,600441129,949857252,439073727,24039072,259332041,397036887,700444570,982525948,540757579,18833638,153964444,134647207,293889516,574399527,783661302,785469917,214684701,946129453,606499613,495641410,68304814,498498460,838049872,570430527,748028022,229177636,770758047,717709679,828854524,493430027,406423258,677011185,564880496,332097684,796184208,823067867,26113515,389409481,651756834,20048735,263600910,179558504,479951636,554377748,36262063,325046611,136518290,578256982,585096089,8966674,894971541,98601651,861988288,426915788,169507116,936725433,374597033,708112946,882579470,585023412,430104091,103817480,158956697,804622657,269917425,175391531,623343150,964850990,795960406,732089698,211001341,486496125,903598418,265349237,612562401,436438957,651420507,96358480,341122138,756278859,290557763,879670628,170888619,139707417,421943912,142323559,268980581,887863538,284354868,842215220,469026240,383120925,94530818,871305403,472644871,858307276,439705073,494635703,519493461,572002304,422926957,566589493,539372193,969089172,314512103,740216641,528432427,298650467,145145366,608276308,804027552,859597112,374616063,50201189,780403523,39800419,171027468,30438898,516504837,643822968,306173829,7347631,11413992,369930247,980730565,367655521,611918315,557257843,209005928,995901960,161564971,524315795,687867948,531915471,439968102,179510903,276517329,356826776,680670939,471125068,361931695,14916385,918037171,196961493,217911398,403627900,798915779,489387205,991769414,104758916,984759446,14323897,813975954,940370358,526405329,700582020,936561591,398555873,58288578,691803172,997613930,104510640,703743519,772635937,295346441,864167319,205181592,295550042,310228193,859747876,926422521,844601018,986320464,868080326,64631735,123870430,895825080,618319566,806010139,850170040,827393248,879455377,509515319,777284508,739654739,5187178,558533504,671534426,490908040,223225138,97506454,972872784,966902861,274774128,980674063,228342684,698721275,734312205,602280268,84567764,142991644,757933867,40173733,838007307,800416988,230904628,981164975,151134349,66523156,496878529,900573660,790708370,472426407,610871583,702476002,718357646,334146508,909749751,788374849,348238305,335097283,827061249,673220339,74174077,386792917,807930706,760127546,304888954,187897703,173659406,865955668,518899017,509841077,898070371,765192883,306059553,386847781,30755059,771293492,964584004,158476992,268759241,488652175,922274025,754620808,229476821,985337444,344707618,551828053,221944475,525227628,81031651,515720459,646713910,468671019,673880582,475725638,857393752,839986228,247757072,827032714,76551256,712524808,};

template <unsigned M> ModInt<M> factorial(long long n) {
  assert(n >= 0);
  if (n >= static_cast<long long>(M)) return 0;
  const long long pos = n / FACTORIAL_STEP;
  const long long m0 = pos * FACTORIAL_STEP;
  const long long m1 = m0 + FACTORIAL_STEP;
  if (m1 < static_cast<long long>(M) && n - m0 > m1 - n) {
    ModInt<M> prod = 1;
    for (long long i = m1; i > n; ) prod *= i--;
    return FACTORIAL[pos + 1] / prod;
  } else {
    ModInt<M> prod = FACTORIAL[pos];
    for (long long i = m0; i < n; ) prod *= ++i;
    return prod;
  }
}

template <unsigned M> void precalc() {
  printf("constexpr ModInt<%u> FACTORIAL[] = {", M);
  ModInt<M> prod = 1;
  for (int n = 0, i = 0; n < static_cast<int>(M); n += FACTORIAL_STEP) {
    for (; i < n; ) prod *= ++i;
    printf("%u,", prod.x);
  }
  printf("};\n");
}

void unittest() {
  constexpr unsigned MO = 998244353U;
  assert(factorial<MO>(0).x == 1U);
  assert(factorial<MO>(1).x == 1U);
  assert(factorial<MO>(2).x == 2U);
  assert(factorial<MO>(100).x == 35305197U);
  assert(factorial<MO>(499999).x == 140694225U);
  assert(factorial<MO>(500000).x == 832944090U);
  assert(factorial<MO>(500001).x == 342650725U);
  assert(factorial<MO>(999999).x == 595392237U);
  assert(factorial<MO>(1000000).x == 373341033U);
  assert(factorial<MO>(1000001).x == 14807739U);
  assert(factorial<MO>(MO - 1).x == MO - 1);
  assert(factorial<MO>(MO).x == 0U);
  assert(factorial<MO>(MO + 1).x == 0U);
}

int main() {
  // precalc<998244353>();
  // precalc<1'000'000'007>();
  // precalc<1'000'000'009>();
  unittest();
  return 0;
}