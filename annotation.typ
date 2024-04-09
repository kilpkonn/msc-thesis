Rust on üldotstarbeline programmeerimiskeel nii süsteemi kui ka rakenduste tarkvara loomiseks.
Erinevalt teistest programmeerimiskeeltest suudab Rust garanteerida turvalise mälu kasutuse kasutamata spetsiaalset mälu haldurit.
Rust konkureerib programmeerimiskeeltega C ja C++ pakkudes arendajale paremaid tööriistu ja paremat arenduse kogemust ilma järele andmata programmi kiiruses.

Rusti tüübi süsteem sarnaneb funktsionaalsete keelte tüübisüsteemidele sisaldades algebralisi andmetüüpe.
Arendaja kogemus Rustis sarnaneb seetõttu rohkem kogemusele kõrgematasemelistes funktsionaalsetes programmeerimiskeeltes kui kogemusele C/C++ arenduses.
Samas Rustis puudub hetkel tööriist, mis suudaks automaatselt genereerida avaldisi, mis vastavad oodatud tüübile.
Sellised tööriistad on tavalised funktsionaalsetes programmeerimiskeeltes ja me usume, et ka Rustil on taolisest tööriistast kasu.

Käesolevas töös arendame edasi Rusti ametlikku tööriista `rust-analyzer`, lisades sellele võimekuse genereerida avaldisi tüüpide alusel.
Lisaks programmide genereerimisele uurime, kas avaldise otsingut on võimalik kasutada ka targema automaatse sõnalõpetuse loomiseks.
Me arendame oma algoritmi kolme iteratsioonina.
Esimene iteratsioon on kõige lihtsam ja sarnaneb suuresti algoritmile mida kasutatakse Agsys, sarnases tööriistas Agda jaoks.
Teises iteratsioonis arendame algoritmi edasi muutes otsingu suuna vastupidiseks.
Sooritades otsingut vastupidises suunas saame lihtsalt lisada vahepealsete väärtuste puhverdamise ning teisi optimeerimisi.
Viimases versioonis muudame otsingu kahesuunaliseks.
Sooritades otsingut kahes suunas, suudame leida avaldise rohkemates kohtades ilma algoritmi tööd oluliselt aeglustamata.

Töö tulemuste hindamiseks jooksutame me algoritmi 155-l vabavaralisel Rusti programmil.
Kustutame osa olemasolevast lähtekoodist, jättes programmi koodi "augud".
Nüüd kasutame oma algoritmi, et genereerida kood nende aukude jaoks.
Mõõdame kui palju auke suudab algoritm täita ja kui tihti suudab algoritm genereerida tagasi originaalse lähtekoodi.

Töö väljundina saadame oma algoritmi ametlikku `rust-analyzer`'i, et seda saaksid kasutada kõik Rusti arendajad.

Lõputöö on kirjutatud inglise keeles keeles ning sisaldab teksti #context counter(page).at(<end>).first() leheküljel, 
#context counter(heading).at(<conclusion>).first() peatükki,
#context counter(figure.where(kind: image)).final().first() joonist 
#context counter(figure.where(kind: raw)).final().first() koodinäidist ja
#context counter(figure.where(kind: table)).final().first() tabelit.