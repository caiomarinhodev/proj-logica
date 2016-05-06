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
}

sig Hospede {}

sig HospedeCrianca extends Hospede{
}

sig Hospedagem {
	reserva: one Reserva
} -- mesmos fatos de reserva

sig Quarto {
}

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
fact comidas {
	#(Cafe) = 1
	#(Almoco) = 1
	#(Janta) = 1
}

-- Criar Reserva de Tres dias.
sig Reserva {
	tipoAlimentacao: one Alimentacao,
	tipoQuarto: one Quarto,
	titular: one Hospede,
	dependentes: some Hospede
} {
	titular !in HospedeCrianca
	titular in dependentes
-- So pode criar reserva pro futuro
-- titular deve estar em hospedes
-- titular nao pode ser crianca
} -- Se reserva j[a foi feita pelo mesmo hospede.o tipoDeAlimentacao deve ser no minimo meia-pensao.

sig ReservaTresDias extends Reserva {}
sig ReservaCancelada extends Reserva {}

pred hospedeTemUmaReserva[h: Hospede] {
	one h.~dependentes
}

fun reservaDoHospede[h: Hospede] : Reserva {
	dependentes.h
}

fact HospedeFact {
	all h: Hospede | hospedeTemUmaReserva[h]
}

pred show[] {}

run show for 3
