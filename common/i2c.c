//-----------------------------------------------------------------------------
// Willok, June 2018
// Edits by Iceman, July 2018
//
// This code is licensed to you under the terms of the GNU GPL, version 2 or,
// at your option, any later version. See the LICENSE.txt file for the text of
// the license.
//-----------------------------------------------------------------------------
// The main i2c code, for communications with smart card module
//-----------------------------------------------------------------------------
#include "i2c.h"

//	������������
#define	GPIO_RST	AT91C_PIO_PA1
#define GPIO_SCL	AT91C_PIO_PA5
#define GPIO_SDA	AT91C_PIO_PA7

#define SCL_H		HIGH(GPIO_SCL)
#define SCL_L		LOW(GPIO_SCL)
#define SDA_H		HIGH(GPIO_SDA)
#define SDA_L		LOW(GPIO_SDA)

#define SCL_read	(AT91C_BASE_PIOA->PIO_PDSR & GPIO_SCL)
#define SDA_read	(AT91C_BASE_PIOA->PIO_PDSR & GPIO_SDA)

#define I2C_PageSize 8


//	ֱ��ʹ��ѭ������ʱ��һ��ѭ�� 6 ��ָ�48M�� Delay=1 ���Ϊ 200kbps
void I2CSpinDelayClk(uint16_t delay) __attribute__((optimize("O0")));
void I2CSpinDelayClk(uint16_t delay) {
	volatile uint32_t c;
	for (c = delay * 2; c; c--) {};
}

void I2C_init(void) {
	// ���ø�λ���ţ��ر����������������Ĭ�ϸ�
	// Configure reset pin, close up pull up, push-pull output, default high
	AT91C_BASE_PIOA->PIO_PPUDR = GPIO_RST;
	AT91C_BASE_PIOA->PIO_MDDR = GPIO_RST;
  
	// ���� I2C ���ţ�������������©���
	// Configure I2C pin, open up, open leakage
	AT91C_BASE_PIOA->PIO_PPUER = GPIO_SCL | GPIO_SDA;	// ������  Open up the pull up
	AT91C_BASE_PIOA->PIO_MDER = GPIO_SCL | GPIO_SDA;

	// Ĭ��������ȫ������
	// default three lines all pull up
	AT91C_BASE_PIOA->PIO_SODR = GPIO_SCL | GPIO_SDA | GPIO_RST;

	// �������
	// allow output
	AT91C_BASE_PIOA->PIO_OER = GPIO_SCL | GPIO_SDA | GPIO_RST;
	AT91C_BASE_PIOA->PIO_PER = GPIO_SCL | GPIO_SDA | GPIO_RST;
}

#define I2C_DELAY_1CLK 		I2CSpinDelayClk(1)
#define I2C_DELAY_2CLK		I2CSpinDelayClk(2)
#define I2C_DELAY_XCLK(x)	I2CSpinDelayClk((x))

// ���ø�λ״̬
// set the reset state
void I2C_SetResetStatus(uint8_t LineRST, uint8_t LineSCK, uint8_t LineSDA) {
	if (LineRST)
		HIGH(GPIO_RST);
	else
		LOW(GPIO_RST);

	if (LineSCK)
		HIGH(GPIO_SCL);
	else
		LOW(GPIO_SCL);

	if (LineSDA)
		HIGH(GPIO_SDA);
	else
		LOW(GPIO_SDA);
}

// ��λ����������
// Reset the SIM_Adapter, then  enter the main program
// Note: the SIM_Adapter will not enter the main program after power up. Please run this function before use SIM_Adapter.
void I2C_Reset_EnterMainProgram(void) {
	I2C_SetResetStatus(0, 0, 0);		//	���͸�λ��
	SpinDelay(100);
	I2C_SetResetStatus(1, 0, 0);		//	�����λ
	SpinDelay(100);
	I2C_SetResetStatus(1, 1, 1);		//	����������
}

// ��λ��������ģʽ
// Reset the SIM_Adapter, then enter the bootloader program
// Reserve��For firmware update.
void I2C_Reset_EnterBootloader(void) {
	I2C_SetResetStatus(0, 1, 1);		//	���͸�λ��
	SpinDelay(100);
	I2C_SetResetStatus(1, 1, 1);		//	�����λ
}

//	�ȴ�ʱ�ӱ��	
// Wait for the clock to go High.	
bool WaitSCL_H(void) {

	volatile uint16_t count = 5000;

	while (count--)	{
		if (SCL_read) {
			return true;
		}
		I2C_DELAY_1CLK;
	}
	return false;
}

bool I2C_Start(void) {
	
	I2C_DELAY_XCLK(4);
	SDA_H;
	I2C_DELAY_1CLK;
	SCL_H;
	
	if (!WaitSCL_H()) return false;

	I2C_DELAY_2CLK;
	
	if (!SCL_read) return false;
	if (!SDA_read) return false;

	SDA_L; I2C_DELAY_2CLK;
	return true;
}

// send i2c STOP
void I2C_Stop(void) {
	SCL_L; I2C_DELAY_2CLK;
	SDA_L; I2C_DELAY_2CLK;
	SCL_H; I2C_DELAY_2CLK;
	SDA_H;
	I2C_DELAY_2CLK;
	I2C_DELAY_2CLK;
	I2C_DELAY_2CLK;
	I2C_DELAY_2CLK;
}
// Send i2c ACK
void I2C_Ack(void) {
	SCL_L; I2C_DELAY_2CLK;
	SDA_L; I2C_DELAY_2CLK;
	SCL_H; I2C_DELAY_2CLK;
	SCL_L; I2C_DELAY_2CLK;
}

// Send i2c NACK
void I2C_NoAck(void) {
	SCL_L; I2C_DELAY_2CLK;
	SDA_H; I2C_DELAY_2CLK;
	SCL_H; I2C_DELAY_2CLK;
	SCL_L; I2C_DELAY_2CLK;
}

bool I2C_WaitAck(void) {
	SCL_L; I2C_DELAY_1CLK;
	SDA_H; I2C_DELAY_1CLK;
	SCL_H;
	if (!WaitSCL_H())
		return false;

	I2C_DELAY_2CLK;
	if (SDA_read) {
		SCL_L;
		return false;
	}
	SCL_L;
	return true;
}

void I2C_SendByte(uint8_t data)	{
	uint8_t i = 8;

	while (i--) {
		SCL_L; I2C_DELAY_1CLK;
		
		if (data & 0x80)
			SDA_H;
		else
			SDA_L;
		
		data <<= 1;
		I2C_DELAY_1CLK;

		SCL_H;
		if (!WaitSCL_H())
			return;

		I2C_DELAY_2CLK;
	}
	SCL_L;
}

uint8_t I2C_ReceiveByte(void) {
	uint8_t i = 8, b = 0;

	SDA_H;
	while (i--)	{
		b <<= 1;
		SCL_L; I2C_DELAY_2CLK;
		SCL_H;
		if (!WaitSCL_H())
			return 0;

		I2C_DELAY_2CLK;
		if (SDA_read)
			b |= 0x01;
	}
	SCL_L;
	return b;
}

// д��1�ֽ����� ����д�����ݣ���д���ַ���������ͣ�
// Writes 1 byte data (Data to be written,command to be written , SlaveDevice address  ).
bool I2C_WriteByte(uint8_t data, uint8_t device_cmd, uint8_t device_address) {
	bool bBreak = true;
	do 	{
		if (!I2C_Start())
			return false;

		I2C_SendByte(device_address & 0xFE);

		if (!I2C_WaitAck())
			break;

		I2C_SendByte(device_cmd);
		if (!I2C_WaitAck())
			break;

		I2C_SendByte(data);
		if (!I2C_WaitAck())
			break;

		bBreak = false;
	} while (false);

	if (bBreak)	{
		I2C_Stop();
		DbpString("I2C_WaitAck Error\n");
		return false;
	}

	I2C_Stop();
	return true;
}


//	д��1�����ݣ���д�������ַ����д�볤�ȣ���д���ַ���������ͣ�	
// Write 1 strings of data (Array address, length, command to be written , SlaveDevice address  ).
// len = uint8 (max buffer to write 256bytes)
bool I2C_BufferWrite(uint8_t *data, uint8_t len, uint8_t device_cmd, uint8_t device_address) {
	bool bBreak = true;

	do {
		if (!I2C_Start())
			return false;

		I2C_SendByte(device_address & 0xFE);

		if (!I2C_WaitAck())
			break;

		I2C_SendByte(device_cmd);

		if (!I2C_WaitAck())
			break;

		while (len) {
			I2C_SendByte(*data);

			if (!I2C_WaitAck())
				break;

			len--;
			data++;		
		}

		if (len == 0)
			bBreak = false;
	} while (false);

	if (bBreak)	{
		I2C_Stop();
		DbpString("I2C_WaitAck Error\n");
		return false;
	}

	I2C_Stop();
	return true;	
}

// ����1�����ݣ���Ŷ������ݣ����������ȣ���������ַ���������ͣ�
// read 1 strings of data (Data storage array, Readout length, command to be written , SlaveDevice address  ).
// len = uint8 (max buffer to read 256bytes)
uint8_t I2C_BufferRead(uint8_t *data, uint8_t len, uint8_t device_cmd, uint8_t device_address) {
	bool bBreak = true;
	uint8_t	readcount = 0;

	// sending
	do {
		if (!I2C_Start())
			return 0;

		I2C_SendByte(device_address & 0xFE);

		if (!I2C_WaitAck())
			break;

		I2C_SendByte(device_cmd);
		if (!I2C_WaitAck())
			break;

		I2C_Start();
		I2C_SendByte(device_address | 1);
		if (!I2C_WaitAck())
			break;

		bBreak = false;
	} while (false);

	if (bBreak)	{
		I2C_Stop();
		DbpString("I2C_WaitAck Error\n");
		return 0;
	}

	// reading
	while (len) {
		len--;
		*data = I2C_ReceiveByte();
		// ��ȡ�ĵ�һ���ֽ�Ϊ��������	
		// The first byte read is the message length
		if (!readcount && (len > *data))
			len = *data;

		if (len == 0)
			I2C_NoAck();
		else
			I2C_Ack();

		data++;
		readcount++;
	}
	
	I2C_Stop();
	return readcount;
}

void i2c_print_status(void) {
	DbpString("Smart card module (ISO 7816)");

	I2C_init();
	I2C_Reset_EnterMainProgram();
	// get version
	uint8_t resp[3] = {0};
	uint8_t len = I2C_BufferRead(resp, 3, I2C_DEVICE_CMD_GETVERSION, I2C_DEVICE_ADDRESS_MAIN);
	if ( len == 3)
		Dbprintf("  FW version................v%x.%02x", resp[1], resp[2]);
}