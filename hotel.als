--Duvidas
-- O Hotel tem um numero limitado de Hospedes? Sim Numero pequeno
-- No quarto Triplo, pode se hospedar quantas pessoas no m[inimo? Pode se hospedar uma
-- Uma crian;a pode estar hospedade sozinha? Nao
-- No completo, todas as refeicoes significa cafe almoco e janta? Sim
-- FUncoes: PegarAlimentacao, pegarQuarto
-- Conjunto de reservas canceladas existe
-- Alimentacao [e pra cada pessoa ou pro quarto? quarto
-- Crianca tem um Responsavel? Nao
-- Reserva eh individual ou feita pra um quarto? quarto
-- Pode ter soh crianca em um quarto? Nao
-- Se tiver uma crianca num quarto, precisa ter o responsavel nela? Nao, soh precisa ter adulto
-- Precisa colocar Cartao de Credito? Ja que essa eh a unica forma de fazer uma reserva
---------- Reserva usa cartao de credito, pois existe hospedagem
-- Tem que criar uma Hospedagem, pois a reserva nao significa que esta hospedado.
-- Criancas nao diminuem as vagas dos adultos.

--open util/ordering [Time]
--sig Time {}

sig Hotel {
	hospedagens: set Hospedagem,
	hospedes: set Hospede,
	reservas: set Reserva,
	quartos: some Quarto
} {#(Hotel) = 1}

sig Hospede {}
sig HospedeCrianca extends Hospede{}

sig Hospedagem {
	titular: one Hospede,
	reserva: lone Reserva,
	tipoQuarto: one Quarto,
	dependentes: some Hospede,
	formaPagamento: one FormaPagamento,
	tipoAlimentacao: one Alimentacao
}

abstract sig FormaPagamento {}
sig Dinheiro extends FormaPagamento {}
sig CartaoCredito extends FormaPagamento {}

abstract sig Quarto {}
sig QuartoDuplo extends Quarto {}
sig QuartoTripo extends Quarto {}

abstract sig Alimentacao {}
sig Cafe {}
sig Almoco  {}
sig Janta {}
sig ApenasCafe extends Alimentacao {
	cafe: one Cafe
}
sig MeiaPensao extends Alimentacao {
	cafe: one Cafe,
	janta: one Janta
}
sig PensaoCompleta extends Alimentacao{
	cafe: one Cafe,
	almoco: one Almoco,
	janta: one Janta
}

sig Reserva {
	tipoAlimentacao: one Alimentacao,
	tipoQuarto: one Quarto,
	titular: one Hospede,
	formaPagamento: one CartaoCredito
}
sig ReservaTresDias extends Reserva {}
sig ReservaCancelada extends Reserva {}

-- Fatos e predicados de Reserva
fact ReservaFact {
	all r: Reserva |
		r.titular !in HospedeCrianca
		and r in Hotel.reservas
}

-- Fatos e predicados de Hospede
pred hospedeTemUmaHospedagem[h: Hospede] {
	one h.~dependentes
}
pred hospedeTitularReserva[h: Hospede, r: Reserva] {
	r.titular = h
}
pred hospedeTitularHospedagem[h: Hospede, o: Hospedagem] {
	o.titular = h
}
fun hospedagemDoHospede[h: Hospede] : Hospedagem {
	dependentes.h
}
fact HospedeFact {
	all h: Hospede |
		hospedeTemUmaHospedagem[h]
			or
		(some r: Reserva | hospedeTitularReserva[h, r])

	all h: Hospede, r1,r2: Reserva |
		(r1 != r2 and hospedeTitularReserva[h, r1])
			=> !hospedeTitularReserva[h, r2]

	all h: Hospede | h in Hotel.hospedes
}


-- Fatos e predicados de Hospedagem
pred mesmoTitular[h: Hospedagem, r: Reserva] {
	h.titular = r.titular
}
pred mesmoTipoQuarto[h: Hospedagem, r: Reserva] {
	h.tipoQuarto = r.tipoQuarto
}
pred mesmaFormaPagamento[h: Hospedagem, r: Reserva] {
	h.formaPagamento = r.formaPagamento
}
pred mesmoTipoAlimentacao[h: Hospedagem, r: Reserva] {
	h.tipoAlimentacao = r.tipoAlimentacao
}
fact HospedagemFact {
	all h: Hospedagem, r: Reserva |
		(h.reserva = r => mesmoTitular[h, r])
		and
		(mesmoTitular[h, r]
			=> h.reserva = r and mesmoTipoQuarto[h, r]
				and mesmaFormaPagamento[h, r])
	
	all h: Hospedagem, r: Reserva |
		h.reserva != r => r.titular !in h.dependentes

	all h: Hospedagem |
		h.titular in h.dependentes
		and h.titular !in HospedeCrianca
		and h.reserva !in ReservaCancelada

	all h1,h2: Hospedagem |
		(h1 != h2) => no h1.dependentes & h2.dependentes
}

-- Fatos e predicados de Alimentacao
fact AlimentacaoFacts {
	#(Cafe) = 1
	#(Almoco) = 1
	#(Janta) = 1
	#(ApenasCafe) = 1
	#(MeiaPensao) = 1
	#(PensaoCompleta) = 1
}

fact ConstantFacts {
	#(Hospede) = 3
	#(Hospedagem) = 0
	#(Reserva) = 3
	#(CartaoCredito) = 1
	#(Dinheiro) = 1
}
pred show[] {}

run show for 5
